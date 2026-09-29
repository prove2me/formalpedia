-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine
-- name    : CerednikDrinfeld.QM.etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/428b7626-e92a-5030-83f3-94254e02df0e
-- title:
--   Edge-chart morphisms of a formally étale uniformisation are étale
-- statement:
--   Fix a prime $r$, a discrete valuation domain $\mathcal O$ with an irreducible element $\pi$ such that $\mathcal O/(\pi)$ has exactly $r$ elements and $(r)=(\pi)$, and a fraction field $K_0$ of $\mathcal O$. Let $O^{\mathrm{nr}}$ be an $\mathcal O$-algebra in which $\pi O^{\mathrm{nr}}$ is maximal and every element $x$ satisfies $p(x)\in\pi O^{\mathrm{nr}}$ for some monic $p\in\mathcal O[T]$. Let $G$ be a type, $f_M\colon M\to\operatorname{Spec}\mathcal O$ a morphism of schemes locally of finite type, and let $\Theta_f$ assign, to every $\mathcal O$-algebra $B$ with $\pi$ nilpotent in $B$, a map from $\bigl((O^{\mathrm{nr}}\to_{\mathcal O}B)\times\{\text{Deligne data over }B\}\bigr)\times G$ to the set of $B$-points of $M$ over $\operatorname{Spec}\mathcal O$; here a Deligne datum attaches to each full $\mathcal O$-lattice $L\subset K_0^2$ a $B$-submodule of $B\otimes_{\mathcal O}L$ with invertible quotient, compatibly with inclusions and homotheties and satisfying the nondegeneracy condition at every prime of $B$. Assume $\Theta_f$ is natural in $B$ (hypothesis `hnat`) and formally étale: for every surjection $p\colon B\to B_0$ of such algebras whose kernel is square-zero (any two elements killed by $p$ have product $0$), every point $x_0$ over $B_0$ and every $B$-point $y$ of $M$ with $p_*y=\Theta_f(x_0)$ lift uniquely to $x$ over $B$ with $p_*x=x_0$ and $\Theta_f(x)=y$. Let $g_1\in\mathrm{GL}_2(K_0)$ be $\operatorname{diag}(\pi,1)$, let $C$ be an $\mathcal O$-algebra with $\pi$ nilpotent, $\psi\colon O^{\mathrm{nr}}\to C$ an $\mathcal O$-algebra map, and let $p_1\colon N\to M$, $p_2\colon N\to\operatorname{Spec}C$ be a pullback of $f_M$ along $\operatorname{Spec}C\to\operatorname{Spec}\mathcal O$. Let $R=\bigl(C[\xi,\eta]/(\xi\eta-\pi)\bigr)$ localised away from the edge discriminant of level $r$, with an $\mathcal O$-algebra structure making $C\to R$ a tower and $\pi$ nilpotent in $R$. Let $d$ be a Deligne datum over $R$ whose line at the standard lattice is $R\cdot(\xi\otimes e_0+1\otimes e_1)$, whose line at $g_1\cdot(\text{standard lattice})$ is the image under base-changed multiplication by $g_1$ of $R\cdot(1\otimes e_0+\eta\otimes e_1)$, and which satisfies the edge-chart nondegeneracy condition `InEdgeChart` at the pair $(g_1\cdot L_{\mathrm{std}},L_{\mathrm{std}})$. Finally let $g\in G$, $h\in\mathrm{GL}_2(K_0)$ and $\theta\colon\operatorname{Spec}R\to N$ be such that $\theta$ followed by $p_1$ is the $R$-point $\Theta_f\bigl((\psi\text{ pushed into }R,\ h\text{-translate of }d),g\bigr)$ and $\theta$ followed by $p_2$ is $\operatorname{Spec}$ of $C\to R$. Then $\theta$ is étale.
--
--   This is the step in Drinfeld's proof of the Čerednik–Drinfeld uniformisation which passes from formal étaleness of the uniformising family $\Theta_f$ to étaleness, as a morphism of schemes, of the induced morphism on a standard edge chart of the formal upper half plane base-changed to $C$; the coefficient component $\mathrm{Hom}_{\mathcal O}(O^{\mathrm{nr}},-)$ is rigid along square-zero extensions, which is what makes the chart over $C$ étale rather than merely formally étale. It feeds the construction of flat families of lifts and the identification of the open locus of points admitting a uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine.lean

import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.QM.etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})

    (G : Type)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪)) [LocallyOfFiniteType fM]
    (Θf : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fM).obj B)
    (hnat :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          Θf B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fM).map φ (Θf B hB x))
    (het :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
          Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
          ∀ (x₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B₀) (y : (Scheme.nilpPoints fM).obj B), (Scheme.nilpPoints fM).map p y = Θf B₀ hB₀ x₀ →
            ∃! x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B, (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ ∧ Θf B hB x = y)

    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

    (C : Type) [CommRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)
    (N : Scheme.{0}) (p₁ : N ⟶ M) (p₂ : N ⟶ Spec (CommRingCat.of C)) (hN : IsPullback p₁ p₂ fM (Scheme.specOver C))

    [Algebra 𝒪 (chartERing C (algebraMap 𝒪 C π) r)] [IsScalarTower 𝒪 C (chartERing C (algebraMap 𝒪 C π) r)]
    (hR : IsNilpotent (algebraMap 𝒪 (chartERing C (algebraMap 𝒪 C π) r) π))

    (d : DeligneDatum (K := K₀) π (chartERing C (algebraMap 𝒪 C π) r))
    (hd₀ : d.line (stdFullLattice K₀) =
      Submodule.span (chartERing C (algebraMap 𝒪 C π) r)
        {(chartERing.ξ C (algebraMap 𝒪 C π) r) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : chartERing C (algebraMap 𝒪 C π) r) ⊗ₜ[𝒪] stdBasisVec K₀ 1})
    (hd₁ : d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
      (Submodule.span (chartERing C (algebraMap 𝒪 C π) r)
        {(1 : chartERing C (algebraMap 𝒪 C π) r) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (chartERing.η C (algebraMap 𝒪 C π) r) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
        (actBaseChange (chartERing C (algebraMap 𝒪 C π) r) g₁ (stdFullLattice K₀)).toLinearMap)
    (hdE : d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀))

    (g : G) (h : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (θ : Spec (CommRingCat.of (chartERing C (algebraMap 𝒪 C π) r)) ⟶ N)
    (hθ₁ : θ ≫ p₁ = (Θf (chartERing C (algebraMap 𝒪 C π) r) hR
      (((IsScalarTower.toAlgHom 𝒪 C (chartERing C (algebraMap 𝒪 C π) r)).comp ψ,
        (Omega.action K₀ π).act (chartERing C (algebraMap 𝒪 C π) r) h d), g)).1)
    (hθ₂ : θ ≫ p₂ = Spec.map (CommRingCat.ofHom (algebraMap C (chartERing C (algebraMap 𝒪 C π) r)))) :
    Etale θ := by sorry
