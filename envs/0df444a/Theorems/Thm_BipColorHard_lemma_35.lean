-- Prove2me | Theorems.Thm_BipColorHard_lemma_35
-- name    : BipColorHard.lemma_35
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:54.611218+00:00
-- url     : https://prove2.me/theorems/4b4a51a0-165e-40e8-a79d-d0bfc97bf198
-- title:
--   Lemma 35 ([GŠV15, Lemma 6.9]) — the finite-port theorem
-- statement:
--   Let $q=2k+1\ge3$ with $D$ as above, $p=D/(D-1)$, and let $\mathcal P$ be the set of global maximizers of $\Psi$. Suppose that:
--
--   1. $\mathcal P$ is finite;
--   2. each $(\alpha,\beta)\in\mathcal P$ has positive coordinates and $\alpha\ne\beta$;
--   3. the Hessian of $\Psi$ is negative definite on the tangent space of the two probability simplices at each maximizer;
--   4. any two maximizers are related by a simultaneous permutation of the colors, possibly followed by interchange of the two vectors.
--
--   Then for every fixed integer $m\ge1$ and $0<\varepsilon<1$, and all sufficiently large $n$, the random graph $\Gamma$ satisfies the following simultaneously with positive probability: $\Gamma$ is simple, and for a uniformly random proper coloring $\sigma$ there is a phase variable $Y=Y(\sigma)\in\mathcal P$ with
--   $$\frac{1-\varepsilon}{|\mathcal P|}\le\Pr[Y=\varphi]\le\frac{1+\varepsilon}{|\mathcal P|}\quad(\varphi\in\mathcal P),$$
--   $$\frac{\Pr[\sigma^+=\tau,\sigma^-=\tau'\mid Y=\varphi]}{\nu_\varphi(\tau,\tau')}\in[1-\varepsilon,1+\varepsilon]\quad(\varphi\in\mathcal P,\ \tau,\tau'\in[q]^m).$$
--
--   It turns information about the maximizers of $\Psi$ into a finite graph whose open vertices are governed by the phases.
--
--   **Formalization Note** The manuscript quotes this from Galanis, Štefankovič and Vigoda (2015) and does not prove it. It is posed as a milestone and is not assumed by the goal theorem.
--
--   Differences from the source:
--   - encoding: with positive probability → there is a point of the uniform finite model; reason: the model is uniform on a finite set
--   - encoding: probabilities under a uniformly random proper coloring → ratios of counts of proper colorings; reason: the coloring space is finite
--   - encoding: all sufficiently large $n$ → $\exists n_0\,\forall n\ge n_0$; reason: the manuscript's $n>m$ holds after enlarging $n_0$
--   - encoding: negative definite Hessian of $\Psi$ → `HessNegDefOnT0`, which includes twice continuous differentiability of the restriction of $\Psi$ to the simplices; reason: a Hessian presupposes it, and Claim 37 supplies it in the manuscript
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Lemma 35, pp.46–47 (PDF pp.48–49), citing [GŠV15, Lemma 6.9]

import Definitions.Def_BipColorHard_Hardness
import Definitions.Def_BipColorHard_RandomGraph

set_option autoImplicit false

namespace BipColorHard

/-- **Lemma 35** ([GŠV15, Lemma 6.9]), pp.46–47 (PDF pp.48–49), manuscript sha256 78a66d1f…, the finite-port theorem,
for `q = 2k + 1 ≥ 3`, `D` of §3, `p = D/(D - 1)`. Let `𝒫` be the set of global maximizers of `Ψ`. Suppose that `𝒫` is finite,
that each `(α, β) ∈ 𝒫` has positive coordinates and `α ≠ β`, that the Hessian of `Ψ` is negative definite on the tangent
space of the two probability simplices at each maximizer, and that any two maximizers are related by a simultaneous
permutation of the colors, possibly followed by interchange of the two vectors. For every fixed integer `m ≥ 1` and
`0 < ε < 1`, and all sufficiently large `n`, the random graph `Γ` satisfies the following with positive probability:
1. `Γ` is simple;
2. for a uniformly random proper coloring `σ` of `Γ`, there is a phase variable `Y = Y(σ) ∈ 𝒫` such that
   `(1 - ε)/|𝒫| ≤ Pr[Y = φ] ≤ (1 + ε)/|𝒫|` for every `φ ∈ 𝒫`;
3. `Pr[σ⁺ = τ, σ⁻ = τ' | Y = φ] / ν_φ(τ, τ') ∈ [1 - ε, 1 + ε]` for every `φ ∈ 𝒫` and `τ, τ' ∈ [q]^m`.

**Formalization Note.** The manuscript quotes this from [GŠV15] and does not prove it; it is posed here as a milestone, not
assumed by the goal. "With positive probability" is the existence of a point of the uniform finite model. Probabilities are
ratios of counts of proper colorings. -/
theorem lemma_35 (k : ℕ) (hk : 1 ≤ k)
    (hfin : (psiMaxSet (2 * k + 1) (bipDeg (2 * k + 1))).Finite)
    (hpos : ∀ φ ∈ psiMaxSet (2 * k + 1) (bipDeg (2 * k + 1)),
      (∀ i, 0 < φ.1 i) ∧ (∀ i, 0 < φ.2 i) ∧ φ.1 ≠ φ.2)
    (hHess : ∀ φ ∈ psiMaxSet (2 * k + 1) (bipDeg (2 * k + 1)),
      HessNegDefOnT0 (psi (bipDeg (2 * k + 1))) φ.1 φ.2)
    (hperm : ∀ φ ∈ psiMaxSet (2 * k + 1) (bipDeg (2 * k + 1)),
      ∀ φ' ∈ psiMaxSet (2 * k + 1) (bipDeg (2 * k + 1)),
      ∃ π : Equiv.Perm (Fin (2 * k + 1)),
        (φ'.1 = φ.1 ∘ π ∧ φ'.2 = φ.2 ∘ π) ∨ (φ'.1 = φ.2 ∘ π ∧ φ'.2 = φ.1 ∘ π))
    (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∃ M : BaseMatchings (bipDeg (2 * k + 1)) n m,
        M.IsSimple ∧
        ∃ Y : BaseColoring (2 * k + 1) M → (Fin (2 * k + 1) → ℝ) × (Fin (2 * k + 1) → ℝ),
          (∀ σ, Y σ ∈ psiMaxSet (2 * k + 1) (bipDeg (2 * k + 1))) ∧
          (∀ φ ∈ psiMaxSet (2 * k + 1) (bipDeg (2 * k + 1)),
            (1 - ε) / ((psiMaxSet (2 * k + 1) (bipDeg (2 * k + 1))).ncard : ℝ) ≤
                (Nat.card {σ // Y σ = φ} : ℝ) / (Nat.card (BaseColoring (2 * k + 1) M) : ℝ) ∧
              (Nat.card {σ // Y σ = φ} : ℝ) / (Nat.card (BaseColoring (2 * k + 1) M) : ℝ) ≤
                (1 + ε) / ((psiMaxSet (2 * k + 1) (bipDeg (2 * k + 1))).ncard : ℝ)) ∧
          ∀ φ ∈ psiMaxSet (2 * k + 1) (bipDeg (2 * k + 1)), ∀ τ τ' : Fin m → Fin (2 * k + 1),
            ((Nat.card {σ : BaseColoring (2 * k + 1) M // σ.OpenAre τ τ' ∧ Y σ = φ} : ℝ) /
                (Nat.card {σ // Y σ = φ} : ℝ)) /
              nuPhi (expP (bipDeg (2 * k + 1))) φ τ τ' ∈ Set.Icc (1 - ε) (1 + ε) := by sorry

end BipColorHard
