-- Prove2me | solution 1 for mme_stothers_phi125_cyclic_mode_word_tuple_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:27:39.708597+00:00
-- url     : https://prove2.me/submissions/9fc68d8b-b5ae-44ad-8bc0-e12d282eb153

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi125_cyclic_hash_data
import Theorems.Thm_mme_stothers_phi125_exact_iff_marginal_profile

open MME.StothersFourth.Phi125

set_option autoImplicit false
set_option warningAsError true

private theorem exactProfile_eq_of_all_modes
    {N alpha beta gamma : ℕ} (hsum : alpha + beta + gamma = N)
    (x y : ExactProfileWord N alpha beta gamma)
    (h0 : modeWord x.1 0 = modeWord y.1 0)
    (h1 : modeWord x.1 1 = modeWord y.1 1)
    (h2 : modeWord x.1 2 = modeWord y.1 2) :
    x = y := by
  apply Subtype.ext
  funext j
  have hpattern :=
    (mme_stothers_phi125_exact_iff_marginal_profile
      N alpha beta gamma hsum).1
  apply hpattern
  funext i
  fin_cases i
  · exact congrFun h0 j
  · exact congrFun h1 j
  · exact congrFun h2 j

theorem solution
    (N alpha beta gamma : ℕ) (hsum : alpha + beta + gamma = N) :
    Function.Injective
      (fun e : MME.StothersFourth.Phi125.CyclicExactEdge
          N alpha beta gamma ↦
        MME.StothersFourth.Phi125.cyclicModeWord e) := by
  intro e f hef
  have hv0 := congrFun hef (0 : Fin 3)
  have hv1 := congrFun hef (1 : Fin 3)
  have hv2 := congrFun hef (2 : Fin 3)
  have he0 : e.1 = f.1 := exactProfile_eq_of_all_modes hsum e.1 f.1
    (congrArg Prod.fst hv0)
    (congrArg Prod.fst hv1)
    (congrArg Prod.fst hv2)
  have he1 : e.2.1 = f.2.1 := exactProfile_eq_of_all_modes hsum e.2.1 f.2.1
    (congrArg (fun q ↦ q.2.1) hv1)
    (congrArg (fun q ↦ q.2.1) hv2)
    (congrArg (fun q ↦ q.2.1) hv0)
  have he2 : e.2.2 = f.2.2 := exactProfile_eq_of_all_modes hsum e.2.2 f.2.2
    (congrArg (fun q ↦ q.2.2) hv2)
    (congrArg (fun q ↦ q.2.2) hv0)
    (congrArg (fun q ↦ q.2.2) hv1)
  exact Prod.ext he0 (Prod.ext he1 he2)
