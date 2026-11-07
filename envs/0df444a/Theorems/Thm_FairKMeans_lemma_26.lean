-- Prove2me | Theorems.Thm_FairKMeans_lemma_26
-- name    : FairKMeans.lemma_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:20.268947+00:00
-- url     : https://prove2.me/theorems/0c79a16d-037e-48ee-9dae-6b0dd444fed0
-- title:
--   Lemma 26 — the LP of an iteration minimizes the linearized cost up to $\tfrac{\eta}{2}L_0$
-- statement:
--   Let $\rho\ge1$, $\varepsilon\in(0,1]$, $\eta=\min\{1/10,\varepsilon/(3\rho)\}$, $L_0\in\mathbb R$, and let $(T,\phi_T)$ be a relaxed solution with $\Psi(\phi_T)\le(1+\lambda)L_0$. Let $(\phi_{T'},z)$ be an optimal solution of LP (29) for $P_\lambda$, $U$ of (26) and the candidate sets $T'=\mathrm{WCS}_{\eta/88}(P_\lambda)$, $V=\mathrm{WCS}_{\eta/4}(U)$. Then $(T',\phi_{T'})$ is a relaxed solution and
--
--   $$L(\phi_{T'})\le L(\phi_{T''})+\frac{\eta}{2}L_0\qquad\text{for every relaxed solution }(T'',\phi_{T''}).$$
--
--   Each iteration therefore approximately solves the Frank–Wolfe subproblem.
--
--   Differences from the source:
--   - generalization: L0 the value of line 2 of Algorithm 1 → any real L0; reason: the proof uses only Ψ(ϕT) ≤ (1+λ)L0; the algorithm's L0 is a special case
--   - encoding: WCS_{η/88}, WCS_{η/4} of Section 4 → the multiset-means sets of Lemma 15, part 2; reason: the set the paper fixes when d is part of the input; used in every dimension
--   - encoding: π(t) of a zero column (undefined) → Lean's 0⁻¹ • 0 = 0, always multiplied by the weight 0; reason: Lean convention; no sum changes
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Lemma 26, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_WeightedKMeans
import Definitions.Def_FairKMeans_RelaxedSolution
import Definitions.Def_FairKMeans_CandidateSets
import Definitions.Def_FairKMeans_LPOracles
import Definitions.Def_FairKMeans_Algorithm1

namespace FairKMeans

/-- **Lemma 26 (The linear program of an iteration)**, p.31 (PDF 33). Cheng–Mo–Song–Ding,
arXiv:2609.07974 (held version, sha256 73e9312c…).

Let `η = min{1/10, ε/(3ρ)}`. Suppose `Ψ(φ_T) ≤ (1+λ)L₀`, and let `(φ_{T'}, z)` be an optimal
solution of LP (29) for `P_λ`, `U` of (26) and the candidate sets `T' = WCS_{η/88}(P_λ)` and
`V = WCS_{η/4}(U)`. Then `(T', φ_{T'})` is a relaxed solution and
`L(φ_{T'}) ≤ L(φ_{T''}) + (η/2)L₀` for every relaxed solution `(T'', φ_{T''})`.

**Formalization Note.** `L₀` is any real number. -/
theorem lemma_26 {d n m s : ℕ} (I : Instance d n m) (ρ ε : ℝ) (hρ : 1 ≤ ρ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (L₀ : ℝ) (φ : Fin n → Fin s → ℝ) (h : IsRelaxed I φ)
    (hΨ : Psi I ρ φ ≤ (1 + lam ρ) * L₀)
    (φ' : Fin n → Fin (n ^ wcsR (eta ρ ε / 88)) → ℝ) (z : Fin (n ^ wcsR (eta ρ ε / 88)) → ℝ)
    (hopt : IsLP29Optimal I (plam I ρ φ) (uvec I ρ φ) (wcs (eta ρ ε / 88) (plam I ρ φ))
      (wcs (eta ρ ε / 4) (uvec I ρ φ)) φ' z) :
    IsRelaxed I φ' ∧
      ∀ (s'' : ℕ) (φ'' : Fin n → Fin s'' → ℝ), IsRelaxed I φ'' →
        linCost I ρ φ φ' ≤ linCost I ρ φ φ'' + eta ρ ε / 2 * L₀ := by sorry

end FairKMeans
