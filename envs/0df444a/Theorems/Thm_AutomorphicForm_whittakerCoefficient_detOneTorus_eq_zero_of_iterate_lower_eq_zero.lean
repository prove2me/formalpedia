-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero
-- name    : AutomorphicForm.whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/9d6c53b8-58d4-5a71-bde9-d1e1a73cbdb1
-- title:
--   Vanishing of the torus Whittaker function on the wrong sheet
-- statement:
--   Let $K$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_K)$, and $w$ a real infinite place of $K$. Let $y\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, left invariant under the unipotents $\begin{pmatrix}1&\beta\\0&1\end{pmatrix}$ with $\beta\in K$, smooth at $w$ in the sense that $e\mapsto y(g\cdot\iota_w(e))$ is $C^\infty$ on $\{\det e\neq 0\}$ for every $g$, and such that every iterated derivative $D_{d_1}\cdots D_{d_r}y$ along the one-parameter flows at $w$ in the directions $H,E,F$ is continuous. Let $\varepsilon=\pm1$, let $k_0,M$ be natural numbers with $k_0\ge 1$, and let $n\in\mathbb{Z}$ satisfy $n=\varepsilon(k_0+2M)$. Assume $D_Ey-D_Fy=(in)\,y$ and $\Omega_w y=\frac{k_0}{2}\bigl(1-\frac{k_0}{2}\bigr)y$, where $\Omega_w=-\bigl(\tfrac14 D_H^2-\tfrac12 D_H+D_ED_F\bigr)$, and that $\mathcal{L}^{M+1}y=0$ for $\mathcal{L}=D_H-\varepsilon i\,(D_E+D_F)$. Let $g_0$ have trivial $\mathrm{GL}_2$-component at $w$. Write $W_1(x)(g)$ for the Whittaker integral $\int x(\begin{pmatrix}1&u\\0&1\end{pmatrix}g)\,\psi(-u)\,d\nu(u)$, with $\psi$ the standard additive character of $\mathbb{A}_K$ and $\nu$ the adelic additive Haar measure conditioned on the box $\mathrm{adelicBox}\,K$ (the prescribed infinite box times the integral finite adeles), the remaining production carrier data being $D$, the levels $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$ and the Hecke generators $\mathrm{heckeGen}(v)$. Assume finally that $\bigl\|W_1(\mathcal{L}^My)\bigl(g_0\,\iota_w\mathrm{diag}(-\varepsilon\sqrt t,\,1/\sqrt t)\bigr)\bigr\|\le C t^{N}$ for all $t\ge 1$, for some $C\in\mathbb{R}$ and $N\in\mathbb{N}$. Then for every $t>0$, $W_1(y)\bigl(g_0\,\iota_w\mathrm{diag}(-\varepsilon\sqrt t,\,1/\sqrt t)\bigr)=0$.
--
--   This is the one-sided support property of the Kirillov–Whittaker function of a discrete-series vector of $\mathrm{GL}_2(\mathbb{R})$: on the sheet of the diagonal torus of sign $-\varepsilon$ the Whittaker function vanishes identically, derived here from the lowest-weight relation $\mathcal{L}^{M+1}y=0$ together with the weight and Casimir eigenvalue equations and moderate growth, rather than from a classification of representations. It feeds the bounds on Whittaker coefficients along the diagonal torus used in identifying the archimedean type of a form, in particular in the Langlands–Tunnell part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hyc : Continuous y)
    (hper : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K), y (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = y g)
    (hys : IsArchSmoothAt hw y)
    (hD : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) y))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (k₀ M : ℕ) (hk₀ : 1 ≤ k₀) (n : ℤ) (hn : (n : ℝ) = ε * (k₀ + 2 * M))
    (hm : archDerivAt hw .E y - archDerivAt hw .Fm y = (Complex.I * n) • y)
    (hΩ : archCasimirAt hw y = (((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2)) • y)
    (hlow : (fun x : AdelicGL2 (𝓞 K) K → ℂ =>
        archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x))^[M + 1] y = 0)
    (g₀ : AdelicGL2 (𝓞 K) K) (hg₀ : archComponent K w (glArch (𝓞 K) K g₀) = 1)
    (C : ℝ) (Ngr : ℕ)
    (hgrowth : ∀ t : ℝ, 1 ≤ t →
      ‖whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (((fun x : AdelicGL2 (𝓞 K) K → ℂ =>
            archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x))^[M] y)) 1
          (g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]))‖ ≤ C * t ^ Ngr)
    (t : ℝ) (ht : 0 < t) :
    whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (y) 1
          (g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹])) = 0 := by sorry
