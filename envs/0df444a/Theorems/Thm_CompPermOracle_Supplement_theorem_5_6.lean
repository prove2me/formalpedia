-- Prove2me | Theorems.Thm_CompPermOracle_Supplement_theorem_5_6
-- name    : CompPermOracle.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:50:20.859879+00:00
-- url     : https://prove2.me/theorems/f7be10ea-e8ef-416b-ab7b-715c2b514529
-- title:
--   Theorem 5.6 — explicit Davies–Meyer preimage and collision security in the ideal cipher model
-- statement:
--   Let $N=2^n$ and let $\Phi=(\varphi_k)_{k\in\mathcal K}$ be an ideal cipher on $\{0,1\}^n$ with an arbitrary finite key space $\mathcal K$: independent uniformly random permutations, with quantum forward and inverse access including superpositions over keys. Consider a quantum algorithm making $q$ queries. A **fixed-target preimage** of $w\in\{0,1\}^n$ is an output $(k,x)$ with $\varphi_k(x)=x\oplus w$; a **collision** is a pair of distinct outputs $(k,x)\ne(k',x')$ with $\mathrm{DM}^\Phi(k,x)=\mathrm{DM}^\Phi(k',x')$, where $\mathrm{DM}^\Phi(k,x)=\varphi_k(x)\oplus x$. Let $T_{\mathrm{pre}}=q+1$ and $T_{\mathrm{col}}=q+3$. Whenever the relevant $T$ satisfies $3T-1\le N$,
--   $$
--   p_{\mathrm{pre}}\le\Big[\frac{2\sqrt2\,a_N(T_{\mathrm{pre}})\,T_{\mathrm{pre}}}{\sqrt N}+e_N(T_{\mathrm{pre}})\Big]^2,\qquad
--   p_{\mathrm{col}}\le\Big[\frac{4\sqrt2\,a_N(T_{\mathrm{col}})\,T_{\mathrm{col}}^{3/2}}{3\sqrt N}+e_N(T_{\mathrm{col}})\Big]^2 .
--   $$
--   For $N\ge16$ and $1\le T\le\sqrt N/4$ (for the relevant $T$), respectively
--   $$
--   p_{\mathrm{pre}}\le\frac{16384(q+1)^2}{2^n},\qquad p_{\mathrm{col}}\le\frac{16(q+3)^3+16384(q+3)^2}{2^n}.
--   $$
--   No bound depends on the number of keys; taking a single key gives the same statements for one random permutation.
--
--   These bounds show that constant success requires $\Omega(2^{n/2})$ queries for a Davies–Meyer preimage and $\Omega(2^{n/3})$ for a collision, with explicit constants.
--
--   **Formalization Note** A singleton key type is the source's single-permutation case and is not stated separately.
--
--   Differences from the source:
--   - generalization: bit strings {0,1}^n as the permutations' domain, N = 2^n → Fin N identified with Fin n → Bool by an arbitrary equivalence e, quantified universally; ⊕ bitwise XOR through e; reason: every fixed bit encoding of the source is one such e; the statement for all e specializes to it
--   - encoding: a q-query algorithm in the ideal cipher model with keys chosen by the adversary and queried in superposition → a published Alg N (K × W) with the accessible key register in the workspace, run for q queries, output map to K × Fin N (resp. pairs of these); probability over uniform Φ : K → S_N; reason: same model as §3.2; a measured output is a function of the computational-basis outcome
--   - encoding: N ≥ 16 and 1 ≤ T ≤ √N/4 for (102), (103), which the source derives from (100), (101) under 3T − 1 ≤ N → 16 ≤ N and (T : ℝ) ≤ √N/4, without 1 ≤ T and without 3T − 1 ≤ N; reason: T = q + 1 or q + 3 is always ≥ 1, and T ≤ √N/4 implies 3T − 1 ≤ N, so neither omitted condition excludes an instance
--   - encoding: 3T − 1 ≤ N; T^{3/2} → 3 * T ≤ N + 1 in ℕ; real power; reason: same instances
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Theorem 5.6, eqs. (100)–(103), p.33 (Davies–Meyer: §3.5, p.10)

import Mathlib
import Definitions.Def_CompPermOracle_Alg
import Definitions.Def_CompPermOracle_Supplement_deltaN
import Definitions.Def_CompPermOracle_Supplement_keyedState
import Definitions.Def_CompPermOracle_Supplement_sponge

namespace CompPermOracle.Supplement

open CompPermOracle

/-- **Theorem 5.6 (Explicit Davies–Meyer security)** (Carolan, Majenz, Compressed Permutation
Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Theorem 5.6,
eqs. (100)–(103), p.33). For a `q`-query algorithm in the ideal cipher model on `{0,1}^n`, `N = 2^n`,
with `T_pre = q + 1` and `T_col = q + 3`: whenever `3T − 1 ≤ N` for the relevant `T`, (100) and
(101) hold; for `N ≥ 16` and `1 ≤ T ≤ √N/4`, (102) and (103) hold. There is no dependence on the
number of keys.

**Formalization Note.** The key space `K` is any finite type (a singleton `K` is the source's
"single random permutation" case). A keyed algorithm is the published `Alg N (K × W)` with the key
register first in the workspace; the probability is over a uniform family `Φ : K → S_N`. `{0,1}^n`
is identified with `Fin N` by an arbitrary equivalence `e`, and `⊕` is bitwise XOR. A preimage of
the fixed target `w` is an output `(k, x)` with `φ_k(x) = x ⊕ w`; a collision is a pair of distinct
outputs `(k, x) ≠ (k', x')` with equal Davies–Meyer values. The source's `1 ≤ T` always holds
(`T ≥ 1`) and is omitted. -/
theorem theorem_5_6 {n N : ℕ} (hN : N = 2 ^ n) (e : (Fin n → Bool) ≃ Fin N) {K W : Type}
    [Fintype K] [DecidableEq K] [Fintype W] [DecidableEq W] (A : Alg N (K × W)) (q : ℕ) :
    (∀ (w : Fin n → Bool) (out : Acc N (K × W) → K × Fin N),
      (3 * (q + 1) ≤ N + 1 →
        keyedSuccess A q out (fun o Φ => e.symm (Φ o.1 o.2) = bxor (e.symm o.2) w) ≤
          (2 * Real.sqrt 2 * aN N (q + 1) * ((q + 1 : ℕ) : ℝ) / Real.sqrt N +
            eN N (q + 1)) ^ 2) ∧
      (16 ≤ N → ((q + 1 : ℕ) : ℝ) ≤ Real.sqrt N / 4 →
        keyedSuccess A q out (fun o Φ => e.symm (Φ o.1 o.2) = bxor (e.symm o.2) w) ≤
          16384 * ((q + 1 : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ n)) ∧
    (∀ out : Acc N (K × W) → (K × Fin N) × (K × Fin N),
      (3 * (q + 3) ≤ N + 1 →
        keyedSuccess A q out
            (fun o Φ => o.1 ≠ o.2 ∧ dm e Φ o.1.1 o.1.2 = dm e Φ o.2.1 o.2.2) ≤
          (4 * Real.sqrt 2 * aN N (q + 3) * ((q + 3 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) /
              (3 * Real.sqrt N) + eN N (q + 3)) ^ 2) ∧
      (16 ≤ N → ((q + 3 : ℕ) : ℝ) ≤ Real.sqrt N / 4 →
        keyedSuccess A q out
            (fun o Φ => o.1 ≠ o.2 ∧ dm e Φ o.1.1 o.1.2 = dm e Φ o.2.1 o.2.2) ≤
          (16 * ((q + 3 : ℕ) : ℝ) ^ 3 + 16384 * ((q + 3 : ℕ) : ℝ) ^ 2) / (2 : ℝ) ^ n)) := by sorry

end CompPermOracle.Supplement
