-- Prove2me | Theorems.Thm_FOMCMonDep_lemma_12_2
-- name    : FOMCMonDep.lemma_12_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:26:09.116415+00:00
-- url     : https://prove2.me/theorems/e8c99178-4a91-4860-9cf8-c23d16430f5a
-- title:
--   Lemma 12.2 (resolve lift) — the type trees after a resolve in time $|G|^2\cdot\mathrm{poly}_{k,q}(M+T)$, of size $\mathrm{poly}_{k,q}(T)$
-- statement:
--   Let $k\ge1$ and $q\in\mathbb N$. Given a partial graph $G$, its distance matrix $D_G$, colors $P,Q$, a sign $\pm$ and the type trees $(\mathrm{tree}^G_{k,q}(a):a\in V(G))$, one can compute $H=\mathrm{resolve}^\pm_{P,Q}(G)$, its distance matrix $D_H$ and $(\mathrm{tree}^H_{k,q}(a):a\in V(G))$ in time
--   $$|G|^2\cdot\mathrm{poly}_{k,q}(M+T),$$
--   where $M=\max_{a\in V(G)}\|\mathrm{tree}^G_{k,q}(a)\|$ and
--   $$T=\max_{a\in V(G)}\bigl|\{\mathrm{tree}^G_{k+i,q-i}(\bar v):0\le i\le q,\ \ell\in[k+i],\ \bar v\in(\mathrm{Ball}^H_{\rho^+(k,q)}(a))^\ell\}\bigr|.$$
--   Each output tree has size $\mathrm{poly}_{k,q}(T)$.
--
--   This is the step of the dynamic programming that handles resolves, which bring far vertices close.
--
--   **Formalization Note** $k$ and $q$ are fixed before the program. The input is the code of $G$, $D_G$, $P$, $Q$, the sign and the tree codes; the output cells begin with the codes of $H$, $D_H$ and the trees of $H$. $|G|$ is the number of vertices.
--
--   Differences from the source:
--   - encoding: an algorithm (RAM model) → one program of the published TrulySubcubicAPSP word RAM with a word-size factor b, correct at every word size W ≥ b(⌊log₂(N+2)⌋+1), N the input length plus its largest absolute entry; reason: the paper's standard RAM with logarithmic word size; the exponents are RAM-specific
--   - encoding: G, D_G, P, Q, ±, the trees as input; H, D_H, the new trees as output → PartialGraph.code, distCode (∞ as −1), P, Q, the sign as 1/0, treesCode; the output cells begin with the codes of H, D_H and the trees of H; reason: fixed input/output layout of the mission
--   - reading: time |G|² · poly_{k,q}(M + T); output size poly_{k,q}(T) → a·n²·(M + T + 2)^e + c steps; output trees of size ≤ (T + 2)^e; reason: poly is (x + 2)^{O(1)} (§3); the additive c covers n = 0, where the literal bound 0 cannot be met by a run, which takes at least one step
--   - encoding: a partial graph (finite vertex set, E and N disjoint, a partition into named colors) → PartialGraph n: vertex set Fin n, color : Fin n → ℕ (one color per vertex), E and N disjoint simple graphs; reason: every finite partial graph has a copy on some Fin n; Part III names the colors by a countable set (p.38)
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Lemma 12.2, p.47 (PDF 49)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_FOMCMonDep_DecidesWithin
import Definitions.Def_FOMCMonDep_treeCode

set_option autoImplicit false

open TrulySubcubicAPSP

namespace FOMCMonDep

/-- **Lemma 12.2 (resolve lift).** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §12, p.47 (PDF 49): "Let k ⩾ 1 and q ∈ N. Given a
partial graph G, its distance matrix D_G, colors P, Q, a sign ±, and (tree^G_{k,q}(a) : a ∈ V(G)), one can compute
H = resolve^±_{P,Q}(G), its distance matrix D_H, and (tree^H_{k,q}(a) : a ∈ V(G)) in time |G|² · poly_{k,q}(M + T),
where M := max_{a∈V(G)} ∥tree^G_{k,q}(a)∥, T := max_{a∈V(G)} |{tree^G_{k+i,q−i}(v̄) : 0 ⩽ i ⩽ q, ℓ ∈ [k + i],
v̄ ∈ (Ball^H_{ρ⁺(k,q)}(a))^ℓ}|. Each output tree has size poly_{k,q}(T)."

**Formalization Note.** `k` and `q` are fixed first ("Let k ⩾ 1 and q ∈ N"), then the program `P` and its word-size
factor `bw`. Input: the code of `G` (`n`, colors, `E`, `N`), `D_G` (`∞` as `−1`), `P`, `Q`, the sign (`1` for
`+`, `0` for `−`), then the trees `tree^G_{k,q}(a)` in their canonical codes; output: the codes of `H`, `D_H` and the
trees of `H`, accepted. `|G|` is the vertex count `n`. The time is `a · n² · (M + T + 2)^e + c`: `poly_{k,q}` is
`(x + 2)^e` (§3, p.11), the factor `a` is absorbed by it, and the additive `c` covers `n = 0`, where a run still
takes a step. The output-size clause is `∥tree^H_{k,q}(a)∥ ⩽ (T + 2)^e`. `T` counts the distinct codes of old trees
(in `G`) of tuples from the balls of `H`; it is finite, so `ncard` is exact. Colors `P = Q` and empty colors are
allowed. -/
theorem lemma_12_2 (k q : ℕ) (hk : 1 ≤ k) :
    ∃ (P : List Instr) (bw e a c : ℕ), ∀ (n : ℕ) (G : PartialGraph n) (Pc Qc : ℕ) (pos : Bool),
      let H := G.resolve pos Pc Qc
      let M := (Finset.univ : Finset (Fin n)).sup fun v => treeSize G k q [v]
      let T := (Finset.univ : Finset (Fin n)).sup fun v =>
        {τ : List ℤ | ∃ i ≤ q, ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ k + i ∧ ∃ w : List (Fin n), w.length = ℓ ∧
          (∀ x ∈ w, x ∈ H.ball (rhoPlus k q) v) ∧ τ = treeCode G (q - i) (k + i) w}.ncard
      let input := G.code ++ G.distCode ++ [(Pc : ℤ), (Qc : ℤ), if pos then 1 else 0] ++ treesCode G k q
      (∀ W : ℕ, WordSizeOK bw input W →
        MonDepMW.RunsWithin P W (a * n ^ 2 * (M + T + 2) ^ e + c) input fun out =>
          Emits out (H.code ++ H.distCode ++ treesCode H k q)) ∧
      ∀ v : Fin n, treeSize H k q [v] ≤ (T + 2) ^ e := by sorry

end FOMCMonDep
