-- Prove2me | Theorems.Thm_BlockchainTFM_theorem_2
-- name    : BlockchainTFM.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:55.288833+00:00
-- url     : https://prove2.me/theorems/84ba5169-6ae1-4755-9ade-df479a374ebd
-- title:
--   Theorem 2: an admissible variation term added to an auxiliary mechanism gives a U-BNIC and 1-SCP TFM
-- statement:
--   Let valuations be i.i.d. from a law $V_0$ on $[0,1]$. Let $\tilde M=(\mathbf a,\tilde{\mathbf p},\tilde r)$ be a transaction fee mechanism and $T=(\boldsymbol\theta,\tilde r)$ a variation term such that
--
--   1. $T$ is **admissible** (Definition 8): $\tilde r(b_i,\mathbf b_{-i})-\tilde r(0,\mathbf b_{-i})=\theta_i(b_i,\mathbf b_{-i})$ and $\mathbb E_{\mathbf b_{-i}\sim V_{-i}}[\theta_i(b_i,\mathbf b_{-i})]=0$;
--   2. the auxiliary mechanism $M=(\mathbf a,\mathbf p,0)$, with $\mathbf p$ the dominant association (7) of $\mathbf a$, forms an **auxiliary-variation decomposition** with $T$ (Definition 7): $\mathbf a$ is monotone non-decreasing in each own bid, $\tilde p_i=p_i+\theta_i/a_i$, and $\theta_i=0$ wherever $a_i=0$.
--
--   Then the composed mechanism $\tilde M=M+T$ is U-BNIC and 1-SCP.
--
--   This is the paper's design principle: any monotone allocation, paired with its dominant association, can be perturbed by an admissible variation term to give the miner revenue $\tilde r$ without losing Bayesian incentive compatibility or 1-side-contract-proofness. Mechanisms 2 and 3 are built this way.
--
--   **Formalization Note** As in Definition 1, the allocation takes values in $[0,1]$ on $[0,1]^n$. Because (7) involves $\partial a_i/\partial t$, $s\mapsto a_i(s,\mathbf b_{-i})$ is assumed differentiable on $[0,1]$ with interval-integrable derivative. The expectations in the definition of U-BNIC are assumed to exist: user $i$'s utility under $\tilde M$ is integrable in $\mathbf b_{-i}$ for every bid and value in $[0,1]$.
--
--   Differences from the source:
--   - reading: ∂a_i(t,b_{−i})/∂t in (6), with no regularity stated → s ↦ a_i(s,b_{−i}) differentiable on [0,1] (one-sided at 0 and 1) with interval-integrable derivative, for every i and b_{−i} ∈ [0,1]^{n−1}; reason: the formula presupposes the derivative; Mechanism 3's allocation is smooth in the own bid
--   - encoding: the expectations in Definition 4 (and (11)) are written without an integrability condition → user i's utility under M̃ and θ_i(b_i,·) are integrable against V₀^{⊗n}; reason: integrability only excludes the case where the expectations are undefined
--   - generalization: V₀ has a pdf ρ on [0,1] → any probability measure V₀ on ℝ with V₀([0,1]) = 1; reason: the proof uses no density; every law with a pdf on [0,1] is an instance
--   - reading: c-SCP with c = 1 (Definition 6) → IsOneSCP: the miner and user i cannot raise u_i + r by changing user i's bid, ex post; reason: the deviation the paper analyses (Lemma EC.3)
--   - encoding: users 1,…,n; b_{−i}; bids and values in [0,1] → Fin n; a vector b ∈ [0,1]ⁿ whose i-th entry is overwritten (Function.update); bids, values and deviations in Set.Icc 0 1; reason: Lean convention; same instances
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, §4.2, Theorem 2, p.23 (Definitions 7–8 p.22; proof Appendix EC.4.1, pp.ec10–ec11)

import Mathlib
import Definitions.Def_BlockchainTFM_Model
import Definitions.Def_BlockchainTFM_Properties
import Definitions.Def_BlockchainTFM_Decomposition

open MeasureTheory

namespace BlockchainTFM

/-- **Theorem 2**, Chen–Simchi-Levi–Zhao–Zhou, arXiv:2209.13099v7, p.23. Suppose the variation
term `T = (θ, r̃)` is admissible (Definition 8). For any auxiliary mechanism `M = (a, p, 0)` that
forms an auxiliary-variation decomposition with `T` (Definition 7), the composed TFM
`M̃ = M + T = (a, p̃, r̃)` is U-BNIC and 1-SCP.

**Formalization Note.** `M̃` is given by its three rules (`Mt`), with `Mt.rev = r̃`; its
allocation takes values in `[0,1]` on `[0,1]ⁿ`, as Definition 1 requires of every TFM (`hrange`);
`IsAuxVarDecomp Mt θ` says `a` is monotone and `p̃ = p + θ/a` with `p` the dominant association
(7) of `a` and `θ = 0` where `a = 0`. Because (7) uses `∂a_i/∂t`, `s ↦ a_i(s, b_{-i})` is
assumed differentiable on `[0,1]` with interval-integrable derivative (as in Lemma 1). The
expectations in the definition of U-BNIC are assumed to exist (`hint`); `V₀` is a probability
law carried by `[0,1]`. -/
theorem theorem_2 {n : ℕ} (V₀ : Measure ℝ) [IsProbabilityMeasure V₀]
    (hV₀ : V₀ (Set.Icc 0 1) = 1) (Mt : TFM n) (θ : (Fin n → ℝ) → Fin n → ℝ)
    (hrange : ∀ i : Fin n, ∀ b ∈ bidBox n, Mt.alloc b i ∈ Set.Icc (0 : ℝ) 1)
    (hadm : IsAdmissible V₀ θ Mt.rev) (hdec : IsAuxVarDecomp Mt θ)
    (hdiff : ∀ i : Fin n, ∀ b ∈ bidBox n,
      DifferentiableOn ℝ (fun s => Mt.alloc (Function.update b i s) i) (Set.Icc 0 1) ∧
        IntervalIntegrable
          (derivWithin (fun s => Mt.alloc (Function.update b i s) i) (Set.Icc 0 1)) volume 0 1)
    (hint : ∀ i : Fin n, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun b => utility Mt i (Function.update b i x) v)
        (Measure.pi fun _ : Fin n => V₀)) :
    IsUBNIC V₀ Mt ∧ IsOneSCP Mt := by sorry

end BlockchainTFM
