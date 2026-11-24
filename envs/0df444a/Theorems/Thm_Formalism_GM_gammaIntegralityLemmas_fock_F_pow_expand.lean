-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_F_pow_expand
-- name    : Formalism.GM.gammaIntegralityLemmas.fock_F_pow_expand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:57.700902+00:00
-- url     : https://prove2.me/theorems/d9db1ce2-0e2c-48aa-a623-0ce89defa1bd
-- title:
--   gamma Integrality Lemmas: fock F pow expand
-- statement:
--   The gamma Integrality Lemmas construction uses the fock F pow expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1427-L1448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1427-L1448

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ) (ρ : Fin r)

theorem Formalism.GM.gammaIntegralityLemmas.fock_F_pow_expand (hy : ∀ c ∈ univ.erase ρ, w c ≠ e ρ ∧ e c ≠ e ρ)
    (G G' : MvPolynomial σ ℚ_[p]) (j m : ℕ) :
    Formalism.GM.M.fock p ((Formalism.GM.tieF w e ^ j) (X (e ρ) ^ m * G)) ((Formalism.GM.tieF w e ^ j) (X (e ρ) ^ m * G')) =
      ∑ a ∈ range (j + 1), ∑ a' ∈ range (j + 1),
        ∑ β ∈ ((FT w e (univ.erase ρ) ^ (j - a)) G).support,
          ∑ γ ∈ ((FT w e (univ.erase ρ) ^ (j - a')) G').support,
            (((j.choose a : ℕ) : ℚ_[p]) * ((j.choose a' : ℕ) : ℚ_[p]) *
              Formalism.GM.M.fock p ((Dop (w ρ) (e ρ) ^ a) (X (e ρ) ^ m *
                        monomial β (coeff β ((FT w e (univ.erase ρ) ^ (j - a)) G))))
                ((Dop (w ρ) (e ρ) ^ a') (X (e ρ) ^ m *
                  monomial γ (coeff γ ((FT w e (univ.erase ρ) ^ (j - a')) G'))))) := by sorry
