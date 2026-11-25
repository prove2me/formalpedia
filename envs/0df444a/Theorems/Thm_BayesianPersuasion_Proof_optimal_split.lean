-- Prove2me | Theorems.Thm_BayesianPersuasion_Proof_optimal_split
-- name    : BayesianPersuasion.Proof.optimal_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:06:14.222449+00:00
-- url     : https://prove2.me/theorems/1560828d-ebd4-4971-8eec-7dec1ee175c2
-- title:
--   Proof: optimal split
-- statement:
--   A finite optimal splitting, with an explicit conservative ambient-dimension bound.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L138-L161
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean#L138-L161

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω]
open BayesianPersuasion.Proof
variable [TopologicalSpace A] [CompactSpace A] [Nonempty A] [T2Space A]
variable (u v : A → Ω → ℝ)
variable (hu : ∀ ω, Continuous (fun a => u a ω))
variable (hv : ∀ ω, Continuous (fun a => v a ω))
include hu hv

theorem BayesianPersuasion.Proof.optimal_split (p : Belief Ω) :
    ∃ (k : ℕ) (_ : k ≤ Fintype.card Ω + 2) (w : Belief (Fin k))
      (b : Fin k → Belief Ω), BayesPlausible p w b ∧
        splitValue u v w b = concavification u v p.val := by sorry
