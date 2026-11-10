-- Prove2me | Theorems.Thm_ConsModCount_strongly_balanced_has_maltsev
-- name    : ConsModCount.strongly_balanced_has_maltsev
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T07:29:15.912214+00:00
-- url     : https://prove2.me/theorems/35fc3658-2112-4617-9e86-67eb9f05fe9c
-- title:
--   [DR, Lemmas 29 and 5] — strong balance implies a Mal'tsev polymorphism
-- statement:
--   Let $H$ be a finite template on a finite nonempty set $D$. If $H$ is strongly balanced, then $H$ has a Mal'tsev polymorphism.
--
--   The paper quotes this from Dyer and Richerby; it gives the second sentence of part 3 of Theorem 1.
--
--   Differences from the source:
--   - generalization: strong balance implies a Mal'tsev polymorphism, within the standing assumption of §§10–13 that H contains every unary subset → every finite template on a finite nonempty domain; reason: Dyer and Richerby's lemmas are for all templates; the conservative case is the source's
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §10, p.13 (PDF p.14), quoting [DR, Lemmas 29 and 5]

import Definitions.Def_ConsModCount_Balance
import Definitions.Def_ConsModCount_Polymorphism

set_option autoImplicit false

namespace ConsModCount

/-- **[DR, Lemmas 29 and 5]** as stated in Xie, *Conservative Modular Counting at Every Odd Prime*, STOC 2027 submission (manuscript sha256 c673b4cc…), §10, p.13 (PDF p.14): strong balance implies the
existence of a Mal'tsev polymorphism.

**Formalization Note.** Stated for every finite template on a finite nonempty domain, without the
standing conservativity assumption of §§10–13. -/
theorem strongly_balanced_has_maltsev {D : Type} [Fintype D] [DecidableEq D] [Nonempty D] (H : Template D)
    (hSB : StronglyBalanced H) :
    HasMaltsev H := by sorry

end ConsModCount
