-- Prove2me | Theorems.Thm_DynBrooks_lemma_4_3
-- name    : DynBrooks.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:10:41.069547+00:00
-- url     : https://prove2.me/theorems/b493438e-4d53-4f8d-84ca-75c0177509cd
-- title:
--   Lemma 4.3 — sparsity of the auxiliary graph: $\zeta_J(u)=\Omega(f_u/R)$
-- statement:
--   Under the standing assumptions of §4 ($3\le\Delta<n$, maximum degree at most $\Delta$, no $K_{\Delta+1}$, $\ell=\max\{1,\lceil\log(n+T+2)\rceil\}$, $\Delta\ge\ell^{10}$, $R=\ell^2$, $b=\ell^4$, $H=\lfloor\Delta/R\rfloor$, $n$ sufficiently large and the decomposition constants $\eta,\eta_0$ sufficiently small), every auxiliary vertex $u$ satisfies
--
--   $$\zeta_J(u)=\Omega(f_u/R).\tag{3}$$
--
--   The order of constants is: the sparsity constant $c_S$ of $S$, then the smallness bound on $\eta$, then the $\Omega$-constant $c$ and the threshold $n_0$. The statement holds for every auxiliary construction with the properties of §4.1.
--
--   The bound gives the slack used to color $J$ from $[\Delta]$ after the random seeds of §4.2.1.
--
--   Differences from the source:
--   - generalization: the auxiliary construction obtained from [BRW25, HM24] with its random choices → every structure with the properties stated on pp.15–17 (AuxConstruction); reason: the paper's construction is one of them; the proof uses only these properties
--   - generalization: ℓ = Θ(log n) for a polynomial horizon T → ℓ = max{1, ⌈log(n + T + 2)⌉} for every T; reason: polynomial horizons are a special case
--   - encoding: η sufficiently small, n sufficiently large, Ω → ∀ c_S > 0 ∃ η₁ > 0 ∀ η ∈ (0, η₁] ∃ c > 0 ∃ n₀; reason: the order of constants of the proof
--   - generalization: η₀ a sufficiently small fixed constant → every real η₀, chosen after c and n₀; reason: the paper's η₀ is one value; for η small against c_S the separation property holds with a positive constant determined by c_S alone (a vertex of S adjacent to all but t vertices of C has ζ ≤ t + 2η∆; a vertex of another almost-clique has at most η∆ neighbors in C), so c need not depend on η₀
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), Lemma 4.3, p.19 (PDF 21); standing assumptions §3, p.13 (PDF 15) and §4.1, p.15 (PDF 17)

import Mathlib
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynBrooks_Sparsity
import Definitions.Def_DynBrooks_Auxiliary

namespace DynBrooks

open Classical in
/-- **Lemma 4.3** (Sparsity of the auxiliary graph; Mishra, Mukherjee, *Fully Dynamic Brooks Coloring*,
STOC 2027 submission, sha256 6542a9f1…, p.19 (PDF 21)). Every auxiliary vertex `u` satisfies
`ζ_J(u) = Ω(f_u/R)` (3).

**Formalization Note.** Standing assumptions of §4 (pp.13, 15): `3 ≤ ∆ < n`, the graph has maximum degree
at most `∆` and no `K_{∆+1}`, `ℓ = max{1, ⌈log(n + T + 2)⌉}`, `∆ ≥ ℓ^{10}`, `R = ℓ²`, `b = ℓ⁴`,
`H = ⌊∆/R⌋`, `n` sufficiently large and the decomposition constants `η, η₀` sufficiently small. The order
of constants: the sparsity constant `c_S` of `S` (`ζ_G(v) ≥ c_S ∆` on `S`) first, then the smallness
bound `η₁` on `η`, then the `Ω` constant `c` and the threshold `n₀`. The statement holds for **every**
auxiliary construction with the page's properties (`AuxConstruction`, pp.15–17) and every `T`, `η₀`: the
random choices behind the paper's construction are not fixed. -/
theorem lemma_4_3 :
    ∀ cS : ℝ, 0 < cS → ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, 0 < η → η ≤ η₁ →
      ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
        ∀ (n T Δ : ℕ) (η₀ : ℝ), n₀ ≤ n → 3 ≤ Δ → Δ < n → ell n T ^ 10 ≤ Δ →
        ∀ G : SimpleGraph (Fin n), IsBrooks Δ G →
        ∀ A : AuxConstruction G Δ (ell n T) cS η η₀,
        ∀ u : A.Vertex,
          c * (A.weight u.1 : ℝ) / (paramR (ell n T) : ℝ) ≤ sparsity Δ A.J u := by sorry

end DynBrooks
