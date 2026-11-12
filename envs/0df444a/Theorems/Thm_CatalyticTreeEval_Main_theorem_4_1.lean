-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_theorem_4_1
-- name    : CatalyticTreeEval.Main.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:32:11.667857+00:00
-- url     : https://prove2.me/theorems/75674745-6def-4371-8cbc-074f85c476da
-- title:
--   Theorem 4.1 — recursive register evaluation with full output and restoration
-- statement:
--   Consider any uniformly parameterized sequence of valid section-four frames with fixed vector and decoder printers and common multiplier $A$; parameter strings have length at most $2^{As}$. There are one finite machine and positive constants $C_s,C_t,B$ and a positive integer $q$, fixed before all parameter strings, tree heights, instances and register contents.
--
--   For every height $h>0$ and every unrestricted TreeEval instance with label length $\ell$, the machine outputs the entire root label and restores all three initially arbitrary ring registers. It uses at most
--
--   $$C_s\bigl(\ell+h(\operatorname{lg}k+\log_2m)+s\bigr)$$
--
--   free work bits and runs in at most
--
--   $$C_t(Bk)^h(2^\ell+k+d+2^s)^q$$
--
--   charged steps. Sequential input seeks, address translation, readout and final restoration are included. As in Section 4.3, the vector dimension is padded to fit $E=\lceil\ell/\lfloor\log_2m\rfloor\rceil$ output blocks when necessary. The algorithm supplies its own output family; no output-family printer is an input hypothesis. This is the register form used by the catalytic simulation.
--
--   Differences from the source:
--   - encoding: finite binary labels, tuples and printing algorithms with O/poly resource notation → Fin indices, fixed self-delimiting binary encodings and charged finite-machine runs with positive uniform constants; reason: these encode the same objects; constants precede all varying construction parameters and all runs
--   - encoding: parameters and access algorithms uniform in the sense of Remark 3.8 → an arbitrary domain of binary parameter strings, fixed printers with common bound As, and |a|≤2^(As); reason: the source explicitly assumes exponentially bounded input length in its access-time accounting; constants may depend on the fixed interface and A but not on a, sizes or tapes
--   - encoding: three d-dimensional registers, with zero padding assumed without loss of generality in Section 4.3 → registers of dimension max(d,ceil(ℓ/floor(log₂ m)))); reason: makes the proof preamble explicit; matching of 2^ℓ distinct labels bounds the padding by a constant factor of d
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Theorem 4.1, printed p. 21 (PDF p. 23); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Framework

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem theorem_4_1 (F : List Bool → Frame) (domain : Set (List Bool))
    (MV MD : Machine) (A : ℕ) (hA : 0 < A)
    (h : ∀ a ∈ domain, (F a).valid ∧ a.length ≤ 2 ^ (A * (F a).s) ∧ (F a).access a MV MD A) :
    ∃ (M : Machine) (Cs Ct B : ℝ) (q : ℕ),
      0 < Cs ∧ 0 < Ct ∧ 0 < B ∧ 0 < q ∧
      ∀ a ∈ domain, ∀ h : ℕ, 0 < h → ∀ (I : Tree (F a).l h)
        (R : Registers (F a).m (paddedDimension (F a))),
      RegisterComputes M (listCode ((F a).params a) ++ I.encode) (bits (F a).l I.value.val) R
        (Cs * ((F a).l + h * (lg (F a).k + log₂ (F a).m) + (F a).s))
        (Ct * (B * (F a).k) ^ h *
          ((2 : ℝ) ^ (F a).l + (F a).k + (F a).d + (2 : ℝ) ^ (F a).s) ^ q) := by sorry

end CatalyticTreeEval.Main
