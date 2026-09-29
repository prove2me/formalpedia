-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_thetaPt_pt_eq_one_of_forall_act_comm_of_principalRoot_of_ne_zero
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_pt_eq_one_of_forall_act_comm_of_principalRoot_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/a81e8a4e-6908-5ec3-8b1c-400493d39a01
-- title:
--   Theta points commuting with K(L) lie over the identity
-- statement:
--   Fix natural numbers $g,d,n$ and $\delta : \mathrm{Fin}\,g \to \mathbb N$ with all $\delta_i$ nonzero and $\prod_i \delta_i = d$, a commutative ring $S$ in which the image of $d$ is a unit, and a polarised abelian scheme $u$ of type $(g,d,n)$ over $S$: an $S$-scheme $u.f : A \to \operatorname{Spec} S$ with a commutative relative group law $u.L$ on points over varying bases, an abelian-scheme property bundle, all fibres of topological Krull dimension $g$, a family of $2g$ $n$-torsion sections independent and spanning the $n$-torsion of every geometrically algebraically closed fibre, and an invertible module $u.pol$ which is a closed immersion by sections and has geometric fibre $H^0$-rank $d$. Let $K$ be an algebraically closed field and $t : \operatorname{Spec} K \to \operatorname{Spec} S$, and let $L'$ be a relative group law on the base change $\mathrm{pullback.snd}\ u.f\ t$ which is compatible with $u.L$ in the sense that for every scheme $T$, every $t' : T \to \operatorname{Spec} K$ and all sections $P,Q$ of the base change over $t'$, the underlying morphism of $L'.mul\ t'\ P\ Q$ followed by $\mathrm{pullback.fst}\ u.f\ t$ agrees with the morphism underlying the $u.L$-product over $t' \circ t$ of the images of $P$ and $Q$. Let $\mathcal L_0$ be an invertible module on the base change, and $a,b$ natural numbers with $1 \le a+b$ and, if $g>0$, with $a+b$ nonzero in $K$. Assume: the Mumford bundle of $\mathcal L_0$ has trivial kernel, i.e. for every commutative ring $R$, every morphism $\operatorname{Spec} R \to \operatorname{Spec} K$ and every section $y$ over it, local isomorphy on the base of the slice pullback of that Mumford bundle to the tensor unit forces $y$ to be the identity section; and the pullback of $u.pol$ along $\mathrm{pullback.fst}\ u.f\ t$ is, locally over the base, isomorphic to $\mathcal L_0^{\otimes a} \otimes ((\mathrm{negMor})^{*}\mathcal L_0)^{\otimes b}$, where $\mathrm{negMor}$ is the inversion morphism of $L'$. Let $x$ be a map from $\bigl(\prod_i \mathbb Z/\delta_i\bigr)^2$ to sections of $u.f$ over $t$ which sends $0$ to the identity section, is additive for $u.L$, is injective, and hits every section $y$ lying in the kernel of the polarisation (those $y$ for which the slice pullback of the Mumford bundle of $u.pol$ is locally on the base isomorphic to the tensor unit). Let $\theta_0$ assign to each such index $h$ a theta point for $u.f$, $u.L$, $u.pol$ over $t$ — a section together with an isomorphism between the translation pullback of $(\mathrm{pullback.fst}\ u.f\ t)^{*}u.pol$ and itself — with underlying point $x_h$, and let $\theta$ be a theta point whose induced operator on global sections of $(\mathrm{pullback.fst}\ u.f\ t)^{*}u.pol$ commutes with that of every $\theta_0\,h$. Then the underlying point of $\theta$ is the identity section $u.L.one\ t$.
--
--   This is the statement that, over an algebraically closed geometric point at which the polarisation is presented as $\mathcal L_0^{\otimes a}\otimes([-1]^{*}\mathcal L_0)^{\otimes b}$ with $\mathcal L_0$ of trivial kernel, the centre of the theta group consists of scalars: a theta point whose operator commutes with all the operators attached to the points of $K(\mathcal L)$ lies over the identity. It is the geometric-point case used by [`AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_pt_eq_one_of_forall_act_comm_of_isAlgClosed`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_pt_eq_one_of_forall_act_comm_of_isAlgClosed), and rests on the identification of theta-group commutators with values of the level-$(a+b)$ Riemann pairing of $\mathcal L_0$ together with the non-degeneracy of that pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_thetaPt_pt_eq_one_of_forall_act_comm_of_principalRoot_of_ne_zero.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators MonoidalCategory

theorem AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_pt_eq_one_of_forall_act_comm_of_principalRoot_of_ne_zero
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    {S : Type} [CommRing S] (hd : IsUnit ((d : ℕ) : S))
    (u : PolarisedAbelianScheme g d n S)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S))

    (L' : RelativeGroupLaw K (pullback.snd u.f t))
    (hL' : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' (pullback.snd u.f t)),
      (L'.mul t' P Q).1 ≫ pullback.fst u.f t =
        (u.L.mul (t' ≫ t)
          ⟨P.1 ≫ pullback.fst u.f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst u.f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (𝓛₀ : (pullback u.f t).Modules) (a b : ℕ) (hab : 1 ≤ a + b)
    (hm : 0 < g → ((a + b : ℕ) : K) ≠ 0) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hker : Polarisation.KernelTrivial (pullback.snd u.f t) L' 𝓛₀)
    (hroot : Polarisation.LocIsoOnBase (pullback.snd u.f t)
      ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol)
      (Scheme.Modules.tpow 𝓛₀ a ⊗ Scheme.Modules.tpow ((Scheme.Modules.pullback (Polarisation.negMor (pullback.snd u.f t) L')).obj 𝓛₀) b))
    (x : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver t u.f)
    (hx0 : x 0 = u.L.one t) (hx : ∀ h h' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), x (h + h') = u.L.mul t (x h) (x h'))
    (hxinj : Function.Injective x)
    (hxK : ∀ y : SchemeHomOver t u.f, Polarisation.MemKernel u.f u.L u.pol t y → ∃ h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), y = x h)
    (θ₀ : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ThetaPt u.f u.L u.pol t) (hθ₀ : ∀ h, (θ₀ h).pt = x h)
    (θ : ThetaPt u.f u.L u.pol t)
    (hcomm : ∀ (h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)),
      θ.act ((θ₀ h).act s) = (θ₀ h).act (θ.act s)) :
    θ.pt = u.L.one t := by sorry
