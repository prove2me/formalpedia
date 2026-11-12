-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_theorem_4_4
-- name    : CatalyticTreeEval.Main.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:31:10.348059+00:00
-- url     : https://prove2.me/theorems/b44cab75-1bbe-4642-88a1-fc3836c789a6
-- title:
--   Theorem 4.4 — one-level algorithm and all resource bounds
-- statement:
--   Consider any uniformly parameterized sequence of valid section-four frames and output families, with fixed vector, decoder and output printers using at most $As$ work bits. The common positive integer $A$ also bounds parameter-string length by $2^{As}$. There are one finite oracle machine, positive constants $C_s,C_r,C_t$ and a positive integer $q$, fixed before any parameter string, gate table, hidden labels, scalar or register contents.
--
--   For every such choice the machine realizes the literal Section 4.2 program, updates only the target by $\alpha W_{f(x_0,x_1)}$ in net, and restores both child registers with exact inverse pairs. Its query count is exactly
--
--   $$4k+4.$$
--
--   Between queries it uses at most $C_s(\ell+s+\operatorname{lg}k)$ work bits, retains at most $C_r(\operatorname{lg}k+\log_2m)$ bits across a query, and runs in at most $C_t(2^\ell+k+d+2^s)^q$ charged steps. Oracle queries address register positions even after swaps, and hidden labels cannot be read by ordinary transitions. This is the computational contract needed for recursive composition.
--
--   Differences from the source:
--   - encoding: finite binary labels, tuples and printing algorithms with O/poly resource notation → Fin indices, fixed self-delimiting binary encodings and charged finite-machine runs with positive uniform constants; reason: these encode the same objects; constants precede all varying construction parameters and all runs
--   - encoding: parameters and access algorithms uniform in the sense of Remark 3.8 → an arbitrary domain of binary parameter strings, fixed printers with common bound As, and |a|≤2^(As); reason: the source explicitly assumes exponentially bounded input length in its access-time accounting; constants may depend on the fixed interface and A but not on a, sizes or tapes
--   - encoding: local state retained across queries → a work prefix with cleared scratch and input/register heads reset at suspension; reason: resetting and recomputing counters fits the stated space and polynomial time and rules out hidden caller state in head positions
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Theorem 4.4, printed p. 22 (PDF p. 24); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Framework

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem theorem_4_4 (F : List Bool → Frame)
    (W : (a : List Bool) → Label (F a).l → Vec (F a).m (F a).d)
    (domain : Set (List Bool)) (MV MD MW : Machine) (A : ℕ) (hA : 0 < A)
    (h : ∀ a ∈ domain, (F a).valid ∧ a.length ≤ 2 ^ (A * (F a).s) ∧
      (F a).access a MV MD A ∧ OutputAccess (F a) (W a) a MW A) :
    ∃ (P : OracleMachine) (Cs Cr Ct : ℝ) (q : ℕ),
      0 < Cs ∧ 0 < Cr ∧ 0 < Ct ∧ 0 < q ∧
      ∀ a ∈ domain, ∀ (f : Label (F a).l → Label (F a).l → Label (F a).l)
        (x : Fin 2 → Label (F a).l) (α : ZMod (F a).m) (R : Registers (F a).m (F a).d),
        let ops := oneLevelProgram (F a).U (F a).V (W a) (F a).D f x α R
        execute (F a).U (F a).V x R ops = addAt R 2 (α • W a (f (x 0) (x 1))) ∧
        InversePairs ops ∧
        (ops.filter (fun op => match op with | .query _ _ _ => true | _ => false)).length =
          4 * (F a).k + 4 ∧
        OracleExecution P (F a).U (F a).V x (oneLevelInput (F a) a f) α R ops
          (Cs * ((F a).l + (F a).s + lg (F a).k))
          (Cr * (lg (F a).k + log₂ (F a).m))
          (some (Ct * ((2 : ℝ) ^ (F a).l + (F a).k + (F a).d + (2 : ℝ) ^ (F a).s) ^ q))
          none := by sorry

end CatalyticTreeEval.Main
