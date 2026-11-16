-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_Supplement_corollary_4_3
-- name    : CatalyticTreeEval.Main.Supplement.corollary_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:38:10.679591+00:00
-- url     : https://prove2.me/theorems/c5954348-d1ba-4ce8-a326-3e1d1fb93727
-- title:
--   Corollary 4.3 (used in the proof of Theorem 3.4) — ordinary-space framework conversion
-- statement:
--   In the binary framework of Section 4, let $m>1$, $\ell\ge1$, $0\in S$, let $S$ be 2-noncancelling, let $U,V$ be an $S$-matching family of exact size $2^\ell$ and dimension $d$, and let the decoder for $S+S$ have sparsity $k$. Assume the uniform vector and term access procedures use common space $s\ge\log_2(dm)$. There is an ordinary binary machine with no catalytic storage that outputs every root bit and, for every $h\ge1$, uses
--   $$S_{\mathrm{ord}}\le C_s\bigl(d\log_2m+\ell+h(L(k)+\log_2m)+s\bigr),\qquad T\le C_t(Bk)^h(2^\ell+k+d+2^s)^q.$$
--   The positive constants and fixed integer degree $q$ are uniform over the input frames and trees for the fixed access procedures. All three ring registers, address state and emulation storage count as ordinary workspace. This result supports both Corollaries 4.9 and 4.10.
--
--   Differences from the source:
--   - encoding: asymptotic algorithmic resource bounds → a finite binary machine and positive uniform constants, with fixed polynomial degrees where needed; reason: expands O/poly using actual transitions and visited work cells; constants precede varying inputs and tapes
--   - encoding: uniform access algorithms and common space s in the section setting → a parameterized frame, two fixed binary printers, a common bound A, and auxiliary-parameter length at most 2^(A s); reason: makes Remark 3.8 access and input-size conventions explicit; constants depend on the fixed access procedures, never on their inputs
--   - encoding: log k in bookkeeping → L(k)=1+log₂(k+1); reason: equivalent for k≥2; at k=1 the extra constant is absorbed by log m since m>1
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Corollary 4.3, printed p. 22 (PDF p. 24)

import Definitions.Def_CatalyticTreeEval_Main_Framework

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

theorem corollary_4_3 (F : List Bool → CatalyticTreeEval.Main.Frame) (domain : Set (List Bool))
    (MV MD : Machine) (A : ℕ) (hA : 0 < A)
    (h : ∀ a ∈ domain, (F a).valid ∧ a.length ≤ 2 ^ (A * (F a).s) ∧ (F a).access a MV MD A) :
    ∃ (M : Machine) (Cs Ct B : ℝ) (q : ℕ),
      0 < Cs ∧ 0 < Ct ∧ 0 < B ∧ 0 < q ∧
      ∀ a ∈ domain, ∀ h : ℕ, 0 < h → ∀ I : Tree (F a).l h,
      PrintsIn M (listCode ((F a).params a) ++ I.encode) (bits (F a).l I.value.val)
        (Cs * ((F a).d * log₂ (F a).m + (F a).l +
          h * (lg (F a).k + log₂ (F a).m) + (F a).s))
        (Ct * (B * (F a).k) ^ h *
          ((2 : ℝ) ^ (F a).l + (F a).k + (F a).d + (2 : ℝ) ^ (F a).s) ^ q) := by sorry

end CatalyticTreeEval.Main.Supplement
