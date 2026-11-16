-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_Supplement_theorem_4_11
-- name    : CatalyticTreeEval.Main.Supplement.theorem_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:41:30.936207+00:00
-- url     : https://prove2.me/theorems/d25966a0-844d-4f2d-8fa1-27fe7de3901e
-- title:
--   Theorem 4.11 (companion theorem; not used in the proof of the goal) — variable-arity register algorithm
-- statement:
--   In the arity-$r$ framework, for every integer $r\ge2$, take $m>1$, a positive label length $\ell$, an $r$-noncancelling score set $S$ containing zero, an $S$-matching family of exact size $2^\ell$ and dimension $d$, and an $rS$-decoder of sparsity $k$. Let fixed uniform access procedures have common space $s\ge\log_2(dm)$. A single deterministic binary machine evaluates every complete ordered $r$-ary tree of every positive height $h$, outputs all root bits, and restores all $r+1$ initially arbitrary dimension-$d$ ring registers. Its simultaneous bounds are
--   $$S\le C_s\bigl(r\ell+h(L(k)+\log_2m+\log_2r)+s\bigr),$$
--   $$T\le C_t2^{C_r h\log_2r}(Bk)^h(2^{r\ell}+k+d+2^s)^q.$$
--   All positive constants and the integer degree $q$ precede the varying arity, frames, trees and register contents. There is no upper bound on $r$ relative to $\ell$. This companion theorem extends the binary framework and supplies the higher-arity bound used in blocking.
--
--   Differences from the source:
--   - encoding: asymptotic algorithmic resource bounds → a finite binary machine and positive uniform constants, with fixed polynomial degrees where needed; reason: expands O/poly using actual transitions and visited work cells; constants precede varying inputs and tapes
--   - encoding: uniform access algorithms and common space s in the section setting → a parameterized frame, two fixed binary printers, a common bound A, and auxiliary-parameter length at most 2^(A s); reason: makes Remark 3.8 access and input-size conventions explicit; constants depend on the fixed access procedures, never on their inputs
--   - encoding: r-ary trees and r+1 registers of dimension d → Fin r child positions, lexicographic full tables and binary serialization of exactly r+1 original-dimension registers; reason: encodes the same data, extends the published binary preorder, and charges any initialized zero padding to local workspace
--   - encoding: log k in bookkeeping → L(k)=1+log₂(k+1); reason: the additive constant is absorbed by log m and log r for m>1 and r≥2
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Theorem 4.11, printed p. 28 (PDF p. 30)

import Definitions.Def_CatalyticTreeEval_Main_Supplement_HigherFramework

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

theorem theorem_4_11 (F : List Bool → Frame) (domain : Set (List Bool))
    (MV MD : Machine) (A : ℕ) (hA : 0 < A)
    (h : ∀ a ∈ domain, (F a).valid ∧ a.length ≤ 2 ^ (A * (F a).s) ∧ (F a).access a MV MD A) :
    ∃ (M : Machine) (Cs Ct Cr B : ℝ) (q : ℕ),
      0 < Cs ∧ 0 < Ct ∧ 0 < Cr ∧ 0 < B ∧ 0 < q ∧
      ∀ a ∈ domain, ∀ h : ℕ, 0 < h →
      ∀ (I : ArityTree (F a).r (F a).l h)
        (R : Registers (F a).r (F a).m (F a).d),
      RegisterComputes M (listCode ((F a).params a) ++ I.encode) (bits (F a).l I.value.val) R
        (Cs * ((F a).r * (F a).l +
          h * (lg (F a).k + log₂ (F a).m + log₂ (F a).r) + (F a).s))
        (Ct * exp₂ (Cr * h * log₂ (F a).r) * (B * (F a).k) ^ h *
          ((2 : ℝ) ^ ((F a).r * (F a).l) + (F a).k + (F a).d + (2 : ℝ) ^ (F a).s) ^ q) := by sorry

end CatalyticTreeEval.Main.Supplement
