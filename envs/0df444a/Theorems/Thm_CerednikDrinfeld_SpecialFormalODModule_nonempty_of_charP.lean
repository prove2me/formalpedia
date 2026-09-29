-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_nonempty_of_charP
-- name    : CerednikDrinfeld.SpecialFormalODModule.nonempty_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/f15b8b2d-a26e-53f3-bdd3-08c1563287d7
-- title:
--   Existence of special formal mathcal O_D-modules over characteristic p rings
-- statement:
--   Let $p$ be a prime, let $B$ be a commutative ring of characteristic $p$, and let $j$ be a ring homomorphism from $\mathbb Z_{p^2} = W(\mathbb F_{p^2})$, realised as [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17) $=$ `WittVector p (GaloisField p 2)`, to $B$. The assertion is that the type [`CerednikDrinfeld.SpecialFormalODModule p j`](def/CerednikDrinfeld_SpecialFormalModule.html#L403) is nonempty, i.e. that there exists such a structure over $B$. Its data consist of a commutative formal group law $F$ in two variables over $B$, a family of power series $\mathrm{act}(a)$ indexed by $a \in \mathbb Z_{p^2}$ and a further power series $\varpi$, all of them endomorphisms of $F$ (the predicate `IsLawHom F F`), subject to: $\mathrm{act}(1)$ is the identity, $\mathrm{act}(ab)$ is the composite of $\mathrm{act}(a)$ and $\mathrm{act}(b)$, $\mathrm{act}(a+b)$ is the sum of $\mathrm{act}(a)$ and $\mathrm{act}(b)$ formed using the group law $F$, $\varpi$ composed with itself equals $\mathrm{act}(p)$, and $\varpi \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \varpi$ for all $a$, where $\sigma$ is the Witt vector Frobenius; together with the two conditions that $F$ be special for $j$, meaning that the two submodules `lieZero` and `lieOne` attached to $j$ are complementary ($\mathrm{IsCompl}$) and each an invertible $B$-module, and that $F$ have height $4$ in the sense that $\mathrm{act}(p)$ has kernel of degree $p^4$ (`HasKernelOfDegree`).
--
--   This is the existence half of Drinfeld's classification of special formal $\mathcal O_D$-modules of height $4$, $\mathcal O_D$ being the maximal order of the quaternion division algebra over $\mathbb Q_p$, stated here over an arbitrary base of characteristic $p$ rather than over an algebraically closed field. It feeds the combined existence, isogeny and centraliser statement [`CerednikDrinfeld.SpecialFormalODModule.nonempty_and_exists_isIsogenyOfHeight_and_exists_ringHom_centralizer_of_isAlgClosed`](thm.html#CerednikDrinfeld.SpecialFormalODModule.nonempty_and_exists_isIsogenyOfHeight_and_exists_ringHom_centralizer_of_isAlgClosed) used in the Čerednik–Drinfeld description of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_nonempty_of_charP.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.nonempty_of_charP
    (p : ℕ) [Fact p.Prime] (B : Type u) [CommRing B] [CharP B p]
    (j : CerednikDrinfeld.Zp2 p →+* B) :
    Nonempty (CerednikDrinfeld.SpecialFormalODModule p j) := by sorry
