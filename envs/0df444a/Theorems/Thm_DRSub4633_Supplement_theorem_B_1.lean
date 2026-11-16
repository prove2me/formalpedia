-- Prove2me | Theorems.Thm_DRSub4633_Supplement_theorem_B_1
-- name    : DRSub4633.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T18:36:54.147198+00:00
-- url     : https://prove2.me/theorems/bdd4d753-6804-4fb3-a1f3-1fead460a398
-- title:
--   Theorem B.1 — sharp recovery $f(h_\star(x))\ge(2\sqrt3-3)f^+(x)$, bounded affine comparisons, and optimality
-- statement:
--   Let $Q=[0,1]^n$, let $f^+$ be the concave closure (135), let $b_\star=\sqrt3/2$, $\alpha_\star=b_\star/(1+b_\star)=2\sqrt3-3$ and $\Gamma_\star=\alpha_\star^{-1}=1+b_\star+1/(4b_\star)$ (136), let $h_\star$ be the recovery map (137), and let $H(f)$ be the endpoint gradient bound (5).
--
--   **Theorem B.1.** Let $f:Q\to\mathbb R_{\ge0}$ be $C^1$ and DR-submodular, and let $x\in Q$.
--
--   1. **(Sharp recovery.)** $\mathbf 0\le h_\star(x)\le x$ coordinatewise, and
--   $$f(h_\star(x))\ge\alpha_\star f^+(x).\tag{138}$$
--   In particular $h_\star(x)\in K$ for every down-closed set $K$ that contains $x$.
--   2. **(Bounded affine comparison.)** There is a vector $g_x$ with $\partial_if(\mathbf 1)\le(g_x)_i\le\partial_if(\mathbf 0)$ for every $i$, such that for every $o\in Q$
--   $$f(o)\le f^+(x)+\langle g_x,o-x\rangle\le\Gamma_\star f(h_\star(x))+\langle g_x,o-x\rangle,\tag{139}$$
--   and consequently $\|g_x\|\le H(f)$.
--   3. **(Optimality, $n=4$.)** Let $T:[0,1]^4\to[0,1]^4$ be any map with $T(x)\le x$, chosen independently of $f$ (it may be discontinuous, and its coordinates may depend on the whole vector $x$). Let $c$ be a real number with $f(T(x))\ge c\,f^+(x)$ for every nonnegative $C^1$ DR-submodular $f$ on $[0,1]^4$ and every $x\in[0,1]^4$. Then $c\le\alpha_\star$.
--
--   So $\alpha_\star\approx0.4641$ is the best coefficient a deterministic, objective-independent downward recovery map can guarantee relative to the concave closure. The map $h_\star$ attains it in every dimension. Part 2 supplies affine comparison vectors with intercept $\Gamma_\star$, bounded by the endpoint gradients. These vectors are not linear in $f$, unlike the field of Theorem 4.1, which works at the slightly smaller coefficient $\alpha_0$.
--
--   **Formalization Note** Vectors are elements of `EuclideanSpace ℝ (Fin n)`, with the order written coordinatewise. Derivatives are taken within the cube. In part 3, $T$ is quantified before $f$, and nothing beyond $T(Q)\subseteq Q$ and $T(x)\le x$ on $Q$ is assumed.
--
--   Differences from the source:
--   - encoding: f : [0,1]ⁿ → ℝ≥0, C1 and DR-submodular → f a total function on EuclideanSpace ℝ (Fin n), nonnegative on the cube, GeomDRSub.IsDRSubmodular (ContDiffOn ℝ 1 on the cube, derivatives within the cube); reason: Lean convention; values off the cube are never read
--   - encoding: f⁺(x) = sup{E f(O) : O ∈ [0,1]ⁿ a.s., E O = x} → concaveClosure: sSup of ∫ f dμ over probability measures μ concentrated on the cube with ∫ y dμ = x, with the identity and f μ-integrable; reason: the law of O replaces the random vector; both integrability conditions hold automatically for such μ and f continuous on the cube
--   - encoding: gₓ ∈ [∇f(1), ∇f(0)] coordinatewise; ‖gₓ‖ ≤ H(f) as a consequence → ∀ i, pd f i 1 ≤ g i ≤ pd f i 0, and ‖g‖ ≤ HEnd f, both for the same g; reason: same statement with the order written coordinatewise
--   - reading: (iii) maps Tₙ : [0,1]ⁿ → [0,1]ⁿ independent of f with Tₙ(x) ≤ x; optimal 'uniformly over dimensions', 'more precisely' for n = 4 → for every T : ℝ⁴ → ℝ⁴ sending [0,1]⁴ into itself with T(x) ≤ x there, quantified before f, no measurability or continuity, and every real c: if c f⁺(x) ≤ f(T(x)) for every nonnegative C¹ DR-submodular f on [0,1]⁴ and every x ∈ [0,1]⁴, then c ≤ α⋆; reason: this is the theorem's own 'more precisely' statement; only the values of T on the cube are used
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Theorem B.1, pp.53–54 (objects: Eqs. (135)–(137), p.53; H(f): Eq. (5), p.8)

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_GeomDRSub_pd
import Definitions.Def_GeomDRSub_IsDRSubmodular
import Definitions.Def_GeomDRSub_IsDownClosed
import Definitions.Def_DRSub4633_Supplement_alphaStar
import Definitions.Def_DRSub4633_Supplement_GamStar
import Definitions.Def_DRSub4633_Supplement_hStar
import Definitions.Def_DRSub4633_Supplement_concaveClosure
import Definitions.Def_DRSub4633_Supplement_HEnd

namespace DRSub4633.Supplement

/-- **Theorem B.1 (Sharp recovery and bounded affine comparisons).** Aggarwal–Du,
*0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization*,
arXiv:2610.21072, Theorem B.1, pp.53–54: "Let `f : [0, 1]ⁿ → ℝ≥0` be `C1` and DR-submodular. For
every `x ∈ [0, 1]ⁿ` the following statements hold. (i) The map (137) satisfies `0 ≤ h⋆(x) ≤ x`,
`f(h⋆(x)) ≥ α⋆ f⁺(x)`. (138) In particular, `h⋆(x) ∈ K` whenever `x` belongs to a down-closed set
`K`. (ii) There is a vector `gₓ ∈ [∇f(1), ∇f(0)]`, where the interval is coordinatewise, such that
for every `o ∈ [0, 1]ⁿ`, `f(o) ≤ f⁺(x) + ⟨gₓ, o − x⟩ ≤ Γ⋆ f(h⋆(x)) + ⟨gₓ, o − x⟩`. (139)
Consequently `‖gₓ‖ ≤ H(f)`, with `H(f)` defined in (5). (iii) The coefficient `α⋆` is optimal
uniformly over dimensions among deterministic maps `Tₙ : [0, 1]ⁿ → [0, 1]ⁿ` that are independent
of `f` and satisfy `Tₙ(x) ≤ x`. More precisely, if `f(T₄(x)) ≥ c f⁺(x)` for every such `f` on
`[0, 1]⁴` and every `x ∈ [0, 1]⁴`, then `c ≤ α⋆`; thus the bound holds already for `n = 4`. This
includes maps whose coordinates depend on the entire vector `x` and maps that are discontinuous."

The statement is the conjunction of:
1. for every `n`, every nonnegative `C¹` DR-submodular `f` on `Q = [0,1]ⁿ` and every `x ∈ Q`:
   (i) `0 ≤ h⋆(x)ᵢ ≤ xᵢ` for all `i`, `α⋆ f⁺(x) ≤ f(h⋆(x))`, and `h⋆(x) ∈ K` for every
   down-closed `K ∋ x`; (ii) some `g` with `∂ᵢf(1) ≤ gᵢ ≤ ∂ᵢf(0)` for all `i` satisfies both
   inequalities of (139) for every `o ∈ Q`, and `‖g‖ ≤ H(f)`;
2. (iii) for every map `T` sending `[0,1]⁴` into itself with `T(x) ≤ x`, and every real `c`: if
   `c f⁺(x) ≤ f(T(x))` for every nonnegative `C¹` DR-submodular `f` on `[0,1]⁴` and every
   `x ∈ [0,1]⁴`, then `c ≤ α⋆`.

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)` with coordinatewise order written out;
`C¹` DR-submodular is `GeomDRSub.IsDRSubmodular` (derivatives within the cube); `f⁺` is
`concaveClosure` (Eq. (135)), `H(f)` is `HEnd` (Eq. (5)). In (iii) no measurability or continuity
of `T` is assumed, and `T` does not depend on `f` (it is quantified before `f`); only the values
of `T` on `[0,1]⁴` matter. -/
theorem theorem_B_1 :
    (∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ), (∀ y ∈ GeomDRSub.cube n, 0 ≤ f y) →
      GeomDRSub.IsDRSubmodular f → ∀ x ∈ GeomDRSub.cube n,
        ((∀ i, 0 ≤ hStar x i ∧ hStar x i ≤ x i) ∧
          alphaStar * concaveClosure f x ≤ f (hStar x) ∧
          (∀ K : Set (EuclideanSpace ℝ (Fin n)), GeomDRSub.IsDownClosed K → x ∈ K →
            hStar x ∈ K)) ∧
        (∃ g : EuclideanSpace ℝ (Fin n),
          (∀ i, GeomDRSub.pd f i (WithLp.toLp 2 (fun _ => 1)) ≤ g i ∧
            g i ≤ GeomDRSub.pd f i 0) ∧
          (∀ o ∈ GeomDRSub.cube n,
            f o ≤ concaveClosure f x + inner ℝ g (o - x) ∧
            concaveClosure f x + inner ℝ g (o - x) ≤
              GamStar * f (hStar x) + inner ℝ g (o - x)) ∧
          ‖g‖ ≤ HEnd f)) ∧
    (∀ (T : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)),
      (∀ x ∈ GeomDRSub.cube 4, T x ∈ GeomDRSub.cube 4 ∧ ∀ i, T x i ≤ x i) →
      ∀ c : ℝ,
        (∀ f : EuclideanSpace ℝ (Fin 4) → ℝ, (∀ y ∈ GeomDRSub.cube 4, 0 ≤ f y) →
          GeomDRSub.IsDRSubmodular f →
          ∀ x ∈ GeomDRSub.cube 4, c * concaveClosure f x ≤ f (T x)) →
        c ≤ alphaStar) := by sorry

end DRSub4633.Supplement
