-- Prove2me | Theorems.Thm_AutomorphicForm_gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype
-- name    : AutomorphicForm.gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/b55886f8-1735-5af6-bd7e-957f38303105
-- title:
--   Torus Whittaker system for an SU(2)-string on GL₂(ℂ)
-- statement:
--   Fix $n\in\mathbb{N}$, functions $F_p:\mathrm{GL}_2(\mathbb{C})\to\mathbb{C}$ indexed by $p\in\{0,\dots,n\}$, and scalars $\kappa,\lambda,\lambda'\in\mathbb{C}$. Data $DF$ and $DD$ are assumed to record first and second derivatives along the six real one-parameter flows $\mathrm{H},\mathrm{E},\mathrm{Fm},i\mathrm{H},i\mathrm{E},i\mathrm{Fm}$, where the flow of $\mathrm{H}$ at time $t$ is $\mathrm{diag}(e^{t},e^{-t})$, that of $\mathrm{E}$ is the upper unipotent $\begin{pmatrix}1&t\\0&1\end{pmatrix}$, that of $\mathrm{Fm}$ the lower unipotent, and the three $i$-variants replace $t$ by $it$: $DF_p(d,h)$ is the derivative at $0$ of $t\mapsto F_p(h\cdot\mathrm{flow}_d(t))$, and $DD_p(d',d,h)$ that of $t\mapsto DF_p(d,h\cdot\mathrm{flow}_{d'}(t))$. Writing $\partial_X=\tfrac12(D_X-iD_{iX})$ and $\bar\partial_X=\tfrac12(D_X+iD_{iX})$, the hypotheses $h\Omega$ and $h\Omega'$ state, spelled out in terms of these data, that $-\bigl(\tfrac14\partial_\mathrm{H}\partial_\mathrm{H}-\tfrac12\partial_\mathrm{H}+\partial_\mathrm{E}\partial_\mathrm{Fm}\bigr)F_p=\lambda F_p$ and the same expression in the $\bar\partial$'s equals $\lambda' F_p$, for every $p$ and every $h$. Further, $F_p\bigl(\begin{pmatrix}1&x\\0&1\end{pmatrix}h\bigr)=e^{2\pi i\cdot 2\mathrm{Re}(\kappa x)}F_p(h)$ for all $x\in\mathbb{C}$; $F_p(h\,\mathrm{diag}(\zeta,\zeta^{-1}))=\zeta^{\,n-2p}F_p(h)$ for all unit $\zeta$; and matrix-valued functions $E_1,E_2:\mathbb{R}\to M_{n+1}(\mathbb{C})$ with $E_1(0)=E_2(0)=1$ satisfy, entrywise, $E_1'(0)_{ij}=1$ if $i=j+1$, $=-j(n+1-j)$ if $j=i+1$, else $0$, and $E_2'(0)_{ij}=i$ if $i=j+1$, $=i\,j(n+1-j)$ if $j=i+1$, else $0$, and carry the right translates $F_p(hk)=\sum_{p'}E_1(s)_{p'p}F_{p'}(h)$ whenever $k=\begin{pmatrix}\cos s&-\sin s\\ \sin s&\cos s\end{pmatrix}$, respectively $F_p(hk)=\sum_{p'}E_2(s)_{p'p}F_{p'}(h)$ whenever $k=\begin{pmatrix}\cos s&i\sin s\\ i\sin s&\cos s\end{pmatrix}$. Put $f_m(y)=F_m(\mathrm{diag}(\sqrt y,1/\sqrt y))$ for $m\le n$ (realised as $\mathrm{diag}(e^{z},e^{-z})$ with $z=\tfrac12\log y$) and $f_m=0$ for $m>n$. The conclusion is that for each $p$ the function $f_p$ and its derivative are differentiable on $(0,\infty)$ and that, for all $y>0$, with $q=n-2p$,
--   $$y^2f_p''+(q-1)y f_p'+\Bigl(\tfrac{q(q-4)}4+4\lambda-16\pi^2\|\kappa\|^2y^2\Bigr)f_p+8\pi i\kappa\,y\,f_{p+1}=0$$
--   and
--   $$y^2f_p''-(q+1)y f_p'+\Bigl(\tfrac{q(q+4)}4+4\lambda'-16\pi^2\|\kappa\|^2y^2\Bigr)f_p-8\pi i\bar\kappa\,p(n+1-p)\,y\,f_{p-1}=0,$$
--   the index $p-1$ being taken in $\mathbb{N}$ (its coefficient vanishes when $p=0$).
--
--   This is the Iwasawa-coordinate form of the two Casimir eigenvalue equations at a complex place, for a single $SU(2)$-type of dimension $n+1$ with unipotent character determined by $\kappa$: restricted to the split torus, the system is triangular in the circle weight, the first relation coupling $f_p$ to $f_{p+1}$ and the second to $f_{p-1}$, so that it closes into a second-order scalar equation of $K$-Bessel type at the extreme weights. It is used in the derivation of the shape and the decay of Whittaker coefficients at a complex place, by [`AutomorphicForm.exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String`](thm.html#AutomorphicForm.exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String) and [`AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String`](thm.html#AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype
    (n : ℕ) (F : Fin (n + 1) → GL (Fin 2) ℂ → ℂ) (κ lam lam' : ℂ)
    (DF : Fin (n + 1) → ArchDirComplex → GL (Fin 2) ℂ → ℂ)
    (DD : Fin (n + 1) → ArchDirComplex → ArchDirComplex → GL (Fin 2) ℂ → ℂ)
    (hD : ∀ (p : Fin (n + 1)) (d : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => F p (h * archFlowMatrixComplex d t)) (DF p d h) 0)
    (hDD : ∀ (p : Fin (n + 1)) (d d' : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => DF p d (h * archFlowMatrixComplex d' t)) (DD p d' d h) 0)
    (hΩ : ∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DD p .H .H h - Complex.I * DD p .H .iH h) -
            Complex.I * ((1 / 2 : ℂ) * (DD p .iH .H h - Complex.I * DD p .iH .iH h)))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DF p .H h - Complex.I * DF p .iH h)) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DD p .E .Fm h - Complex.I * DD p .E .iFm h) -
            Complex.I * ((1 / 2 : ℂ) * (DD p .iE .Fm h - Complex.I * DD p .iE .iFm h)))) = lam * F p h)
    (hΩ' : ∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DD p .H .H h + Complex.I * DD p .H .iH h) +
            Complex.I * ((1 / 2 : ℂ) * (DD p .iH .H h + Complex.I * DD p .iH .iH h)))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DF p .H h + Complex.I * DF p .iH h)) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DD p .E .Fm h + Complex.I * DD p .E .iFm h) +
            Complex.I * ((1 / 2 : ℂ) * (DD p .iE .Fm h + Complex.I * DD p .iE .iFm h)))) = lam' * F p h)
    (hN : ∀ (p : Fin (n + 1)) (x : ℂ) (h : GL (Fin 2) ℂ),
      F p (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * ((2 * (κ * x).re : ℝ) : ℂ)) * F p h)
    (hM : ∀ (p : Fin (n + 1)) (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ h : GL (Fin 2) ℂ,
      F p (h * circleGL2 ζ) = (ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * F p h)
    (E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hE₁ : E₁ 0 = 1) (hE₂ : E₂ 0 = 1)
    (hE₁' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₁ s i j)
      (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hE₂' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₂ s i j)
      (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hK₁ : ∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, -Complex.sin s; Complex.sin s, Complex.cos s] →
        F p (h * k) = ∑ p' : Fin (n + 1), E₁ s p' p * F p' h)
    (hK₂ : ∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, Complex.I * Complex.sin s; Complex.I * Complex.sin s, Complex.cos s] →
        F p (h * k) = ∑ p' : Fin (n + 1), E₂ s p' p * F p' h) :
    let f : ℕ → ℝ → ℂ := fun m y =>
      if hm : m < n + 1 then F ⟨m, hm⟩ (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ)) else 0
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0) := by sorry
