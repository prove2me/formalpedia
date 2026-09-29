-- Prove2me | Theorems.Thm_AutomorphicForm_exists_localComponents_of_isGlobalAddChar
-- name    : AutomorphicForm.exists_localComponents_of_isGlobalAddChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/79682157-c3af-57d9-824d-bbd2e864a36b
-- title:
--   Local components of a global additive character of A_F
-- statement:
--   Let $F$ be a number field and let $\psi$ be an additive character of the adele ring $\mathbb{A}_F$ with values in $\mathbb{C}$ which is global in the sense that it is trivial on the image of $F$ under the structure map $F \to \mathbb{A}_F$, is continuous, and is not the trivial character. Then there exist a family of additive characters $\psi_v$ of the completions $F_v$, indexed by the height-one primes $v$ of $\mathcal{O}_F$, integers $n_v$, real numbers $\theta_w$ indexed by the real infinite places and complex numbers $\theta_w$ indexed by the complex infinite places, such that: $\psi_v(x) = 1$ whenever $\mathrm{v}(x) \le \exp(n_v)$ in the value group written multiplicatively; for each $v$ there is an $x$ with $\mathrm{v}(x) \le \exp(n_v + 1)$ and $\psi_v(x) \ne 1$, so $\psi_v$ has exact level $n_v$; the set of $v$ with $n_v \ne 0$ is finite; for every finite adele $x$, the value of $\psi$ on the adele with infinite part $0$ and finite part $x$ equals the finitary product $\prod_v \psi_v(x_v)$; every $\theta_w$ is non-zero; and for every point $p = (p_1,p_2)$ of the mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$, the value of $\psi$ on the adele with finite part $0$ and infinite part corresponding to $p$ equals $\prod_{w \text{ real}} \exp(-2\pi \theta_w p_1(w) i) \cdot \prod_{w \text{ complex}} \exp(-4\pi \,\mathrm{Re}(\theta_w p_2(w)) i)$, both products being finitary.
--
--   This is the classical description, from Tate's thesis, of an arbitrary non-trivial continuous character of $\mathbb{A}_F$ trivial on $F$ as a restricted product of local characters of exact levels given by the different, together with explicit archimedean frequencies; the statement asserts only the existence of the components, levels and frequencies. It is the input to the analysis of Whittaker coefficients of automorphic forms, and is cited throughout the construction of Whittaker functionals and their analytic continuation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_localComponents_of_isGlobalAddChar.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain AutomorphicForm
set_option autoImplicit false

theorem AutomorphicForm.exists_localComponents_of_isGlobalAddChar
    (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ) :
    ∃ (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ) (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
      (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ),
      (∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
        Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1) ∧
      (Function.support nψ).Finite ∧
      (∀ x : FiniteAdeleRing (𝓞 F) F,
        ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
          = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v)) ∧
      (∀ i, θr i ≠ 0) ∧ (∀ w, θc w ≠ 0) ∧
      (∀ p : mixedEmbedding.mixedSpace F,
        ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
          = (∏ᶠ i : {w : InfinitePlace F // w.IsReal},
                Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
            * ∏ᶠ w : {w : InfinitePlace F // w.IsComplex},
                Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I))) := by sorry
