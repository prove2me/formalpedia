-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_reach_of_cuts
-- name    : DeciSigma1.Full.Closure.reach_of_cuts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:06:39.075294+00:00
-- url     : https://prove2.me/theorems/7f142005-dd43-475e-a0b9-bd82fc738c21
-- title:
--   Closure: reach of cuts
-- statement:
--   If the upper run of `p` on a prefix of `u` meets the lower run of `q` on a prefix of `t`, and
--   the rest of `u` is a prefix of the rest of `t`, then `(p, u)` derives `(q, t)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L425-L435
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L425-L435

module
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Automata
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
variable [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (Γ : List (LitT n V))
variable {c Γ}
variable (c Γ)
variable {c Γ}

theorem DeciSigma1.Full.Closure.reach_of_cuts {p q : V × Bool} {u t : List (Fin n)} {i e : ℕ}
    (hi : i ≤ u.length) (he : e ≤ t.length)
    (hpre : (u.drop i).IsPrefix (t.drop e))
    (hg : (Automata.upperRun (signed c Γ) p (u.take i) ∩
      Automata.lowerRun (signed c Γ) q (t.take e)).Nonempty) :
    Reach c Γ (p.1, p.2, u) (q.1, q.2, t) := by sorry
