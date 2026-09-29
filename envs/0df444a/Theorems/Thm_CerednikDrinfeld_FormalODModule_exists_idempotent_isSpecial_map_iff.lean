-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_idempotent_isSpecial_map_iff
-- name    : CerednikDrinfeld.FormalODModule.exists_idempotent_isSpecial_map_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/02089c1d-5e2e-5b22-9796-82719ae005c8
-- title:
--   Speciality of a formal mathcal O_D-module is cut out by an idempotent
-- statement:
--   Let $p$ be a prime, let $S$ be a commutative ring in which the image of $p$ is nilpotent, let $j\colon \mathbb Z_{p^2} = W(\mathbb F_{p^2}) \to S$ be a ring homomorphism, and let $Y$ be a formal $\mathcal O_D$-module over $S$ in the sense of the project's structure `FormalODModule`: a commutative two-variable formal group law $F$ over $S$ together with power-series endomorphisms $\mathrm{act}(a)$ for $a \in \mathbb Z_{p^2}$ and an endomorphism $\varpi$, each a homomorphism of formal group laws for $F$, satisfying $\mathrm{act}(1) = \mathrm{id}$, $\mathrm{act}(ab) = \mathrm{act}(a)\circ\mathrm{act}(b)$, $\mathrm{act}(a+b) = F(\mathrm{act}(a),\mathrm{act}(b))$, $\varpi\circ\varpi = \mathrm{act}(p)$ and $\varpi\circ\mathrm{act}(a) = \mathrm{act}(\sigma a)\circ\varpi$, where $\sigma$ is the Witt-vector Frobenius. The assertion is that there is an idempotent $e \in S$ with the following property: for every commutative ring $S'$ and every ring homomorphism $f\colon S \to S'$, the base change $Y$ along $f$ (obtained by applying `MvPowerSeries.map f` to the group law, to each $\mathrm{act}(a)$ and to $\varpi$) is special relative to $f\circ j$ if and only if $f(e) = 1$. Here "special relative to a map $j'$" means that inside the Lie module of the formal $\mathcal O_D$-module the two submodules $\bigcap_{a}\ker(\mathrm{lieAct}(a) - j'(a))$ and $\bigcap_{a}\ker(\mathrm{lieAct}(a) - j'(\sigma a))$ are complementary and both invertible as modules over the base.
--
--   This is the statement that, for a formal $\mathcal O_D$-module over a base on which $p$ is nilpotent, speciality in the sense of Drinfeld and of Boutot–Carayol is an open and closed condition on the base, represented by an idempotent of the coordinate ring; equivalently, the locus where the two eigen-pieces of the Lie module for the unramified $\mathbb Z_{p^2}$-action both have rank one is a union of connected components. It feeds the local criterion `isSpecial_of_forall_isSpecial_map_away` and the construction of the moduli scheme with its closed immersion into projective space used in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_idempotent_isSpecial_map_iff.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_idempotent_isSpecial_map_iff
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (hS : IsNilpotent (p : S))
    (j : Zp2 p →+* S) (Y : FormalODModule p S) :
    ∃ e : S, IsIdempotentElem e ∧
      ∀ (S' : Type) [CommRing S'] (f : S →+* S'), (Y.map f).IsSpecial (f.comp j) ↔ f e = 1 := by sorry
