-- Prove2me | Theorems.Thm_CritWinSpin_p6b_6_3_proposal_tm
-- name    : CritWinSpin.p6b_6_3_proposal_tm
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:46:12.568515+00:00
-- url     : https://prove2.me/theorems/fb9633c0-cac1-4c05-84bb-808d8289a9a5
-- title:
--   Uniform PPT subset-sum proposal for the independent spin clouds
-- statement:
--   Fix a single-site GHS law $\rho$ of type $p$ and admissible gadget parameters. There is one uniform probabilistic polynomial-time proposal machine which, on every valid input $(H,\hat u,y)$, samples a cloud configuration according to an exactly describable finite law $\tilde\nu_y$.
--
--   The proposal law is a probability distribution, its support is contained in that of the ideal independent-cloud law $\nu_y$, and
--   $$
--   \sum_{\sigma}\left|\tilde\nu_y(\sigma)-\nu_y(\sigma)\right|
--    \le \frac12e^{-2n^2}.
--   $$
--   Here $\nu_y=\prod_i\nu_{y_i}$ and $\beta=\tau+\theta$. The displayed error is the proposal half of the $e^{-2n^2}$ error allowed in step 1 of $\hat L_{T,k}$.
--
--   This isolates the exact subset-sum dynamic program: conditional on an attainable cloud sum, the quadratic exponential factor is constant, so one can count subsets exactly and sample spin by spin, using polynomially many bits for the exponential weights. Support containment is required in addition to the $\ell^1$ bound so that later decoding and rejection cannot create configurations absent from the ideal model.
--
--   **Formalization Note.** The machine is uniform in the entire binary input, with no advice. Its per-configuration probabilities are defined through `PPT.prob` and `decCloud`. The quantification includes $n=0$ and $r=0$; as in the parent theorem, the `IsUhat` premise guards the proposal specification in degenerate cases.
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission #943 (manuscript sha256 f77584da…), §6.2, p.24 (PDF p.25), procedure $\hat L_{T,k}$, step 1: independent-cloud sampling by exact subset-sum counting, spin-by-spin sampling, and polynomial-bit exponential-weight approximation.

import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Lhat
import Definitions.Def_CritWinSpin_nuPm
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp CritWinSpin
set_option autoImplicit false

/-- Step 1 on p.24: one uniform PPT proposal sampler for the independent clouds. -/
theorem CritWinSpin.p6b_6_3_proposal_tm (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    ∀ (w ε : ℝ) (Ac Cc : ℕ), 1 ≤ w → 0 < ε → ε < dExp p → GadgetParams p w ε Ac Cc →
      ∃ propM : PPT,
        ∀ (n : ℕ) (H : Inst n), H.1.IsSymm → (∀ i, H.1 i i = 0) →
          width (castM H.1) (castV H.2) ≤ (n : ℝ) ^ w →
          ∀ (û : ℚ), IsUhat S ((thetaQ p Ac Cc n : ℚ) : ℝ) (cloudSize p Cc n) û →
            ∀ y : BinCfg n,
              ∃ nuT : Config S (Fin n × Fin (cloudSize p Cc n)) → ℝ,
                (∀ σ, 0 ≤ nuT σ) ∧ ∑ σ, nuT σ = 1 ∧
                (∀ σ, propM.prob (tupleCode [encInst H, encRat û, List.ofFn y])
                    (fun s => decCloud S n (cloudSize p Cc n) s = some σ) = nuT σ) ∧
                (∀ σ, 0 < nuT σ →
                  0 < nuProd S (((tauQ S + thetaQ p Ac Cc n : ℚ) : ℝ)) y σ) ∧
                ∑ σ : Config S (Fin n × Fin (cloudSize p Cc n)),
                  |nuT σ - nuProd S (((tauQ S + thetaQ p Ac Cc n : ℚ) : ℝ)) y σ| ≤
                    (1 / 2 : ℝ) * Real.exp (-(2 * (n : ℝ) ^ 2)) := by sorry
