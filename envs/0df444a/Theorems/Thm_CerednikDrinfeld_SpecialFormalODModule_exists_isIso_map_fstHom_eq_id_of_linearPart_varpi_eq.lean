-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/6d9e4736-6bd0-5363-9146-1c19a3a113f8
-- title:
--   Equal varpi-linear part implies strict isomorphism over k[ε]
-- statement:
--   Let $q$ be a prime and $k$ an algebraically closed field of characteristic $q$, let $j_0\colon W(\mathbb F_{q^2})\to k$ be a ring homomorphism, and let $X_0$ be a `SpecialFormalODModule` for $j_0$: a commutative formal group law in two variables over $k$ together with series giving an action of $W(\mathbb F_{q^2})$ and a series $\varpi$ subject to the relations $\varpi\circ\varpi=[q]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$, satisfying `IsSpecial` for $j_0$ and `HasHeight 4`. Assume the linear part of $X_0.\varpi$ — the $2\times 2$ matrix over $k$ of coefficients of the degree-one monomials — annihilates, via `Matrix.mulVecLin`, every element of `lieZero` $j_0$ and of `lieOne` $j_0$, the submodules of the Lie module of $X_0$ cut out by the intersection over $a$ of the kernels of $\mathrm{lieAct}(a)-j_0(a)$, respectively $\mathrm{lieAct}(a)-j_0(\sigma a)$. Let $N,N'$ be formal $\mathcal O_D$-modules over the dual numbers $k[\varepsilon]$ whose pushforwards along $\mathrm{fst}\colon k[\varepsilon]\to k$ are equal to $X_0$ on the nose (law, action series and $\varpi$ alike), and suppose the linear parts of $N.\varpi$ and $N'.\varpi$ coincide in $M_2(k[\varepsilon])$. Then there is a homomorphism $\theta\colon N\to N'$ of formal $\mathcal O_D$-modules admitting a two-sided inverse, whose series reduces modulo $\varepsilon$ to the identity series on $k$.
--
--   This is the injectivity half of the tangent-space computation for the deformation functor of a special formal $\mathcal O_D$-module of height $4$ at a double point, in the Čerednik–Drinfeld uniformisation: the two linear coordinates of $\varpi$ determine a first-order deformation up to strict isomorphism. It is used in establishing that the deformation functor is pro-represented, through `ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hnode₀ : ∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    (hnode₁ : ∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    (N N' : FormalODModule q (DualNumber k))
    (hN : N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule)
    (hN' : N'.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule)
    (hvarpi : MvFormalGroup.linearPart N.varpi = MvFormalGroup.linearPart N'.varpi) :
    ∃ θ : N.Hom N', θ.IsIso ∧ θ.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom = Series.id k := by sorry
