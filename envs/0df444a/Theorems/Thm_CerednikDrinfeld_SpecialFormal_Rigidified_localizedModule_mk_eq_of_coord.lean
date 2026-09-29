-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_localizedModule_mk_eq_of_coord
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.localizedModule_mk_eq_of_coord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/77a6142c-b8a9-561b-89fb-4c1064b5b7e8
-- title:
--   Equality of fractions from agreeing coordinates in a localised submodule
-- statement:
--   Let $p$ be a prime, let $B$ and $B'$ be commutative $\mathbb{Z}_p$-algebras and let $f\colon B\to B'$ be a $\mathbb{Z}_p$-algebra homomorphism. Let $N\subseteq B^2$ and $N'\subseteq B'^2$ be submodules, let $T$ be a $B$-module and $T'$ a $B'$-module, and let $\sigma\colon T\simeq N$ and $\sigma'\colon T'\simeq N'$ be linear equivalences. Let $\tau\colon T\to T'$ be semilinear over $f$ and assume that for all $r\in T$ and $i\in\{0,1\}$ the $i$-th coordinate of $\sigma'(\tau r)$ is $f$ applied to the $i$-th coordinate of $\sigma r$. Fix a prime $x'$ of $B'$, write $x$ for its preimage under $f$, and let $g\in B$ satisfy $g\notin x$ and $f(g)\notin x'$. Let $fg\colon \mathrm{Localization}(\text{powers }g)\to \mathrm{Localization}(\text{powers }f(g))$ be a ring homomorphism with $fg\circ\mathrm{awayHom}(g)=\mathrm{awayHom}(f(g))\circ f$. Let $tt,sQ\in T$, $s\in B$ with $f(s)\notin x'$, and $b$ in the complement of $x$, such that $tt/s=sQ/b$ in the localisation of $T$ at $x$. Let $w\colon \{0,1\}\to B_g$ be such that, for each $i$, the image of the $i$-th coordinate of $\sigma(sQ)$ in $\mathrm{Localization.AtPrime}\,x$ equals the image of $b$ times the image of $w_i$ under the canonical map $B_g\to B_x$. Let $s'\in T'$, let $b'$ lie in the complement of $x'$, and let $w'\colon\{0,1\}\to B'_{f(g)}$ satisfy the analogous relation for the coordinates of $\sigma'(s')$ in $\mathrm{Localization.AtPrime}\,x'$, with $w'_i=fg(w_i)$ for all $i$. Then $s'/b'=\tau(tt)/f(s)$ in the localisation of $T'$ at $x'$.
--
--   A purely commutative-algebraic compatibility statement: two fractions in the stalk at $x'$ of a module identified with a submodule of $B'^2$ coincide once their coordinates, described through a distinguished affine open $\mathrm{Spec}\,B_g$, agree after transport along $f$. It is used in the base-change clause for Cartier quadruples attached to special formal modules, namely by [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.u_baseChange`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.u_baseChange).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_localizedModule_mk_eq_of_coord.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open scoped TensorProduct

theorem CerednikDrinfeld.SpecialFormal.Rigidified.localizedModule_mk_eq_of_coord
    {p : ℕ} [Fact p.Prime]
    {B B' : Type} [CommRing B] [CommRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B'] (f : B →ₐ[ℤ_[p]] B')
    (N : Submodule B (Fin 2 → B)) (N' : Submodule B' (Fin 2 → B'))
    (T : Type) [AddCommGroup T] [Module B T] (T' : Type) [AddCommGroup T'] [Module B' T']
    (σ : T ≃ₗ[B] ↥N) (σ' : T' ≃ₗ[B'] ↥N')
    (τ : T →ₛₗ[(f : B →+* B')] T')
    (hτσ : ∀ (r : T) (i : Fin 2), ((σ' (τ r) : ↥N') : Fin 2 → B') i = f (((σ r : ↥N) : Fin 2 → B) i))
    (x' : PrimeSpectrum B') (g : B) (hg : g ∉ (PrimeSpectrum.comap (f : B →+* B') x').asIdeal)
    (hg' : f g ∉ x'.asIdeal)
    (fg : Rigidified.Baway g →+* Rigidified.Baway (f g))
    (hfg : fg.comp (Rigidified.awayHom g) = (Rigidified.awayHom (f g)).comp (f : B →+* B'))
    (tt sQ : T) (s : B) (hs : f s ∉ x'.asIdeal) (b : (PrimeSpectrum.comap (f : B →+* B') x').asIdeal.primeCompl)
    (heq : LocalizedModule.mk tt
        (⟨s, fun h => hs (by simpa using (Ideal.mem_comap.mp h))⟩ : (PrimeSpectrum.comap (f : B →+* B') x').asIdeal.primeCompl) =
      LocalizedModule.mk sQ b)
    (w : Fin 2 → Rigidified.Baway g)
    (hσb : ∀ i, Rigidified.locHom (PrimeSpectrum.comap (f : B →+* B') x') (((σ sQ : ↥N) : Fin 2 → B) i) =
      Rigidified.locHom (PrimeSpectrum.comap (f : B →+* B') x') (b : B) *
        Rigidified.awayToLoc (PrimeSpectrum.comap (f : B →+* B') x') g hg (w i))
    (s' : T') (b' : x'.asIdeal.primeCompl) (w' : Fin 2 → Rigidified.Baway (f g))
    (hσb' : ∀ i, Rigidified.locHom x' (((σ' s' : ↥N') : Fin 2 → B') i) =
      Rigidified.locHom x' (b' : B') * Rigidified.awayToLoc x' (f g) hg' (w' i))
    (hw : ∀ i, w' i = fg (w i)) :
    LocalizedModule.mk s' b' = LocalizedModule.mk (τ tt) (⟨f s, hs⟩ : x'.asIdeal.primeCompl) := by sorry
