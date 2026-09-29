-- Prove2me | Theorems.Thm_AutomorphicForm_exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen
-- name    : AutomorphicForm.exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/b666521c-f2cc-5981-a29a-2699d141b7fa
-- title:
--   Adelic GL₂ Haar measure against a compact open level
-- statement:
--   Let $K$ be a number field, and let $U'$ be a subgroup of $\mathrm{GL}_2(\mathbb{A}_K^{\mathrm{fin}})$, where $\mathbb{A}_K^{\mathrm{fin}}$ is the finite adele ring of $\mathcal{O}_K$ in $K$, which is assumed compact and open as a subset of $\mathrm{GL}_2(\mathbb{A}_K^{\mathrm{fin}})$. Then there exists a real constant $c>0$ with the following property: for every $\Phi : M_2(\text{mixed space of }K) \to \mathbb{C}$ that is continuous, has compact support, and whose topological support is contained in the set of matrices $E$ with $\det E$ a unit, one has
--   $$\int_{\mathrm{GL}_2(\mathbb{A}_K)} \Phi\bigl(\mathrm{archEntries}(x_\infty)\bigr)\,\mathbf 1_{U'}(x_{\mathrm{fin}})\,d\mu(x) \;=\; c\int_{M_2} \Phi(E)\,\bigl(N(\det E)^{-1}\bigr)^{2}\,dE .$$
--   Here $\mu$ is the Haar measure `AdelicHaar.adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$ for the Borel $\sigma$-algebra, $x_\infty =$ `AdelicLevel.glArch` $(x)$ and $x_{\mathrm{fin}} =$ `AdelicLevel.glFin` $(x)$ are the images of $x$ under the componentwise maps induced by the two projections $\mathbb{A}_K \to K_\infty$ and $\mathbb{A}_K \to \mathbb{A}_K^{\mathrm{fin}}$, `archEntries` transports the matrix entries of an element of $\mathrm{GL}_2(K_\infty)$ to the mixed space of $K$ through the ring isomorphism $K_\infty \cong \prod_{w\ \mathrm{real}}\mathbb{R}\times\prod_{w\ \mathrm{complex}}\mathbb{C}$, the indicator of $U'$ takes the value $1\in\mathbb{C}$ on $U'$ and $0$ elsewhere, $N$ is the norm of the mixed space, and $dE$ is the canonical (product Lebesgue) measure on matrices over the mixed space.
--
--   This is the adelic form of the standard comparison $d^\times g = |\det g|^{-2}\,dg$ between the Haar measure of $\mathrm{GL}_2$ and the additive measure on matrix entries, here packaged for test functions on $\mathrm{GL}_2(\mathbb{A}_K)$ that are the indicator of a compact open level $U'$ in the finite variable; the constant $c$ absorbs the normalisation of the archimedean measure and the finite volume of $U'$. It is used in the analysis of factorizable test functions and their convolution decompositions, and thence in the construction of irreducible admissible constituents of cuspidal automorphic representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm MeasureTheory IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped Classical in

theorem AutomorphicForm.exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen
    (K : Type) [Field K] [NumberField K]
    (U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
    (hU'c : IsCompact (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))))
    (hU'o : IsOpen (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) :
    ∃ c : ℝ, 0 < c ∧
      ∀ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ, Continuous Φ → HasCompactSupport Φ →
        tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} →
          ∫ x, Φ (archEntries K (AdelicLevel.glArch (𝓞 K) K x)) *
              (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ))
                (AdelicLevel.glFin (𝓞 K) K x) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) =
            c * ∫ E, Φ E * (((mixedEmbedding.norm (Matrix.det (Matrix.of E)))⁻¹ ^ 2 : ℝ) : ℂ) := by sorry
