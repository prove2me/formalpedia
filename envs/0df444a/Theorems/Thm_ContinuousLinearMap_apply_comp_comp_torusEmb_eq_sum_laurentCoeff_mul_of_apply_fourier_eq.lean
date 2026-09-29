-- Prove2me | Theorems.Thm_ContinuousLinearMap_apply_comp_comp_torusEmb_eq_sum_laurentCoeff_mul_of_apply_fourier_eq
-- name    : ContinuousLinearMap.apply_comp_comp_torusEmb_eq_sum_laurentCoeff_mul_of_apply_fourier_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/b19adb28-5391-526a-8da3-55b3718997b1
-- title:
--   Laurent expansion of monomials pulled back to the torus
-- statement:
--   Fix a type $\iota_L$, a natural number $d$, a subset $XK \subseteq (\mathbb{C}\times\mathbb{C})^{\mathrm{Fin}\,d}$ and a subset $X \subseteq (\mathbb{C}\times\mathbb{C})^{\iota_L}$. Let $\mathrm{emb} : (\mathrm{AddCircle}\,1)^{\mathrm{Fin}\,d} \to XK$ be continuous with $i$-th coordinate $(\mathrm{fourier}\,1(\theta_i), \mathrm{fourier}(-1)(\theta_i))$ for all $\theta$ and $i$. Let $w' : \mathrm{Fin}\,d \to \iota_L$, let $\rho, s, \zeta, N : \mathrm{Fin}\,d \to \mathbb{C}$ with $N_i \neq 0$ for all $i$, and let $bc : XK \to X$ be continuous such that, for every $x \in XK$ and every $i$, the two components of $(bc\,x)_{w'(i)}$ are $\rho_i s_i (x_{i,1} + x_{i,2})$ and $N_i \zeta_i + (x_{i,1} x_{i,2} - 1)$. Let $\mu$ be a continuous $\mathbb{C}$-linear functional on $C((\mathrm{AddCircle}\,1)^{\mathrm{Fin}\,d}, \mathbb{C})$ and $c : \mathbb{Z}^{\mathrm{Fin}\,d} \to \mathbb{C}$ a function such that $\mu(e) = c(n)$ whenever $e$ is a continuous function given pointwise by $\theta \mapsto \prod_i \mathrm{fourier}(n_i)(\theta_i)$. Finally let $k, j : \mathrm{Fin}\,d \to \mathbb{N}$ and let $g : X \to \mathbb{C}$ be continuous with $g(x) = \prod_i (x_{w'(i)})_1^{k_i}\,(N_i^{-1} (x_{w'(i)})_2)^{j_i}$ for all $x$. Then $\mu$ applied to $\mathrm{emb}$ followed by $bc$ followed by $g$ equals $$\sum_{n \in \prod_i [-k_i, k_i]} \Big(\prod_i (\rho_i s_i)^{k_i} \zeta_i^{j_i}\,[(T^{1}+T^{-1})^{k_i}]_{n_i}\Big)\, c(n),$$ the sum being over the tuples $n$ of integers with $|n_i| \le k_i$, and $[\cdot]_{n_i}$ denoting the $n_i$-th coefficient of the indicated element of the Laurent polynomial ring $\mathbb{C}[T, T^{-1}]$.
--
--   This is the Chebyshev–Laurent expansion of a monomial in Satake-type coordinates after restriction to the compact torus: on the image of the embedding the two coordinates are inverse unit characters, so the monomial becomes a trigonometric polynomial whose Fourier coefficients are the coefficients of $(T+T^{-1})^{k}$. It is used in the construction of a cylinder functional on a box of Satake parameters whose values on monomials are prescribed by such sums.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ContinuousLinearMap_apply_comp_comp_torusEmb_eq_sum_laurentCoeff_mul_of_apply_fourier_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem ContinuousLinearMap.apply_comp_comp_torusEmb_eq_sum_laurentCoeff_mul_of_apply_fourier_eq
    {ιL : Type} (d : ℕ) (XK : Set (Fin d → ℂ × ℂ)) (X : Set (ιL → ℂ × ℂ))
    (emb : C((Fin d → AddCircle (1 : ℝ)), XK))
    (hemb : ∀ (θ : Fin d → AddCircle (1 : ℝ)) (i : Fin d),
      ((emb θ : XK) : Fin d → ℂ × ℂ) i = ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ)))
    (w' : Fin d → ιL) (ρ s ζ N : Fin d → ℂ) (hN : ∀ i : Fin d, N i ≠ 0)
    (bc : C(XK, X))
    (hbc1 : ∀ (x : XK) (i : Fin d), (((bc x : X) : ιL → ℂ × ℂ) (w' i)).1 =
      ρ i * s i * ((((x : XK) : Fin d → ℂ × ℂ) i).1 + (((x : XK) : Fin d → ℂ × ℂ) i).2))
    (hbc2 : ∀ (x : XK) (i : Fin d), (((bc x : X) : ιL → ℂ × ℂ) (w' i)).2 =
      N i * ζ i + ((((x : XK) : Fin d → ℂ × ℂ) i).1 * (((x : XK) : Fin d → ℂ × ℂ) i).2 - 1))
    (μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ) (c : (Fin d → ℤ) → ℂ)
    (hc : ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) → μ e = c n)
    (ks js : Fin d → ℕ) (g : C(X, ℂ))
    (hg : ∀ x : X, g x = ∏ i : Fin d,
      (((x : X) : ιL → ℂ × ℂ) (w' i)).1 ^ ks i * ((N i)⁻¹ * (((x : X) : ιL → ℂ × ℂ) (w' i)).2) ^ js i) :
    μ ((g.comp bc).comp emb) =
      ∑ n ∈ Fintype.piFinset (fun i : Fin d => Finset.Icc (-(ks i : ℤ)) (ks i)),
        (∏ i : Fin d, (ρ i * s i) ^ ks i * ζ i ^ js i *
          ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks i : LaurentPolynomial ℂ).coeff (n i)) * c n := by sorry
