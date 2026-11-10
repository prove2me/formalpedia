-- Prove2me | Theorems.Thm_ConsModCount_carbonnel_minority_term
-- name    : ConsModCount.carbonnel_minority_term
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T07:28:02.509027+00:00
-- url     : https://prove2.me/theorems/aed0dd87-95f1-4b7c-a93b-67fdbdc784a1
-- title:
--   Carbonnel's lemma [BM, Lemma 11] — a conservative Mal'tsev operation generates a conservative minority term
-- statement:
--   Let $D$ be a finite set and $h:D^3\to D$ a conservative Mal'tsev operation. Then some ternary term $t$ in $h$ has a term operation $t^h$ that is a conservative minority operation:
--
--   $$t^h(x,x,y)=t^h(x,y,x)=t^h(y,x,x)=y,\qquad t^h(x,y,z)\in\{x,y,z\}.$$
--
--   Moreover $t^h$ preserves every relation that $h$ preserves.
--
--   The paper quotes this lemma from Bodirsky and Moorhead; it supplies the minority operation on which the algorithm of Theorem 2 runs.
--
--   Differences from the source:
--   - reading: a conservative Mal'tsev operation generates a conservative minority term → some ternary term in the single operation symbol h has a conservative minority term operation; reason: "generates a term" means a term operation of the algebra (D; h)
--   - reading: A term in polymorphisms is again a polymorphism → the chosen term operation preserves every relation (of every template on D) preserved by h; reason: the sentence is used for this term; it holds for every term
--   - generalization: D is the nonempty domain of the template (p.1) → any finite D, empty allowed; reason: at an empty D every operation is vacuously a conservative minority operation, so the statement specializes to the source's on every nonempty D
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §2, p.3 (PDF p.4), quoting [BM, Lemma 11, p.13]

import Definitions.Def_ConsModCount_Polymorphism

set_option autoImplicit false

namespace ConsModCount

/-- **Carbonnel's lemma, [BM, Lemma 11]** as stated in Xie, *Conservative Modular Counting at Every Odd Prime*, STOC 2027 submission (manuscript sha256 c673b4cc…), §2, p.3 (PDF p.4): a conservative
Mal'tsev operation generates a conservative minority term. A term in polymorphisms is again a
polymorphism.

**Formalization Note.** "Generates a term" is read as: some ternary term `t` in the one operation
symbol `h` (`Term3`) has a term operation `t.eval h` that is a conservative minority operation. The
second sentence is stated for this term: it preserves every relation (of every template on `D`)
that `h` preserves. `D` is finite. -/
theorem carbonnel_minority_term {D : Type} [Fintype D] (h : D → D → D → D)
    (hM : IsMaltsev h) (hc : IsConservativeOp h) :
    ∃ t : Term3, IsMinority (t.eval h) ∧ IsConservativeOp (t.eval h) ∧
      ∀ H : Template D, IsPolymorphism H (ternary h) → IsPolymorphism H (ternary (t.eval h)) := by sorry

end ConsModCount
