-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_corollary_4_2
-- name    : CatalyticTreeEval.Main.corollary_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:31:48.816811+00:00
-- url     : https://prove2.me/theorems/80d14bcc-da7d-4b7a-a94c-286a9bfc9e71
-- title:
--   Corollary 4.2 — arbitrary-bit catalytic simulation
-- statement:
--   In any uniformly parameterized section-four setting, with the same fixed access interfaces and exponentially bounded parameter strings as in Theorem 4.1, there are one finite binary machine, positive constants $C_s,C_c,C_t,B$ and a positive integer $q$, uniform over all parameter strings, heights, instances and initial tapes. On every valid TreeEval instance of height $h>0$ the machine outputs all root-label bits and restores every initial catalyst bit. Simultaneously it has bounds
--
--   $$\begin{aligned}\mathrm{free}&\le C_s(\ell+h(\operatorname{lg}k+\log_2m)+s),\\\mathrm{catalytic}&\le\left\lceil C_cd(1+\log_2(dm))\right\rceil,\\\mathrm{time}&\le C_t(Bk)^h(2^\ell+k+d+2^s)^q.\end{aligned}$$
--
--   The guarantee holds for every arbitrary bitstring of at least that catalytic length, with only the bounded prefix addressed. Initial blocks need not encode ring elements. The catalytic factor is $d\log(dm)$, including the representation overhead of Remark 3.3. This realizes register restoration as exact restoration of the original bits.
--
--   Differences from the source:
--   - encoding: finite binary labels, tuples and printing algorithms with O/poly resource notation → Fin indices, fixed self-delimiting binary encodings and charged finite-machine runs with positive uniform constants; reason: these encode the same objects; constants precede all varying construction parameters and all runs
--   - encoding: parameters and access algorithms uniform in the sense of Remark 3.8 → an arbitrary domain of binary parameter strings, fixed printers with common bound As, and |a|≤2^(As); reason: the source explicitly assumes exponentially bounded input length in its access-time accounting; constants may depend on the fixed interface and A but not on a, sizes or tapes
--   - encoding: arbitrary catalytic bits of the prescribed bounded capacity → all longer arbitrary tapes, with every head position strictly inside the rounded bounded prefix; reason: the program cannot sense the suffix or obtain advice from tape length; exact entire-tape equality includes untouched suffixes
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Corollary 4.2, printed p. 21 (PDF p. 23); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Framework

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem corollary_4_2 (F : List Bool → Frame) (domain : Set (List Bool))
    (MV MD : Machine) (A : ℕ) (hA : 0 < A)
    (h : ∀ a ∈ domain, (F a).valid ∧ a.length ≤ 2 ^ (A * (F a).s) ∧ (F a).access a MV MD A) :
    ∃ (M : Machine) (Cs Cc Ct B : ℝ) (q : ℕ),
      0 < Cs ∧ 0 < Cc ∧ 0 < Ct ∧ 0 < B ∧ 0 < q ∧
      ∀ a ∈ domain, ∀ h : ℕ, 0 < h → ∀ I : Tree (F a).l h,
      ComputesPrefix M (listCode ((F a).params a) ++ I.encode) (bits (F a).l I.value.val)
        (Cs * ((F a).l + h * (lg (F a).k + log₂ (F a).m) + (F a).s))
        (Cc * (F a).d * (1 + log₂ ((F a).d * (F a).m)))
        (Ct * (B * (F a).k) ^ h *
          ((2 : ℝ) ^ (F a).l + (F a).k + (F a).d + (2 : ℝ) ^ (F a).s) ^ q) := by sorry

end CatalyticTreeEval.Main
