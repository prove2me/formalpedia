-- Prove2me | solution 1 for tendsto_polynomialSupNorm_atTop_of_antitone_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:33.526071+00:00
-- url     : https://prove2.me/submissions/1c876177-2687-454a-aaa4-42067fd67c2c

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Theorems.Thm_polynomialSupNorm_mono_of_isCompact
import Theorems.Thm_polynomialSupNorm_iInter_eq_iInf_of_antitone_isCompact
import Theorems.Thm_polynomialSupNorm_nonneg


set_option autoImplicit false
open Filter Polynomial Set
theorem _root_.solution
    (p : Polynomial ℂ) (K : ℕ → Set ℂ)
    (hanti : Antitone K)
    (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty) :
    Tendsto (fun n ↦ polynomialSupNorm p (K n)) atTop
      (nhds (polynomialSupNorm p (⋂ n, K n))) := by
  have hManti : Antitone (fun n ↦ polynomialSupNorm p (K n)) := fun _ _ hmn ↦
    polynomialSupNorm_mono_of_isCompact p (hanti hmn) (hcompact _)
  have hMbdd : BddBelow (Set.range fun n ↦ polynomialSupNorm p (K n)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact polynomialSupNorm_nonneg p (K n)
  rw [polynomialSupNorm_iInter_eq_iInf_of_antitone_isCompact p K hanti hcompact hnonempty]
  exact tendsto_atTop_ciInf hManti hMbdd
