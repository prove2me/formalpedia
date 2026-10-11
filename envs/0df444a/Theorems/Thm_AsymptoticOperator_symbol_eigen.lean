-- Prove2me | Theorems.Thm_AsymptoticOperator_symbol_eigen
-- name    : AsymptoticOperator.symbol_eigen
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T22:48:19.556959+00:00
-- url     : https://prove2.me/theorems/0671a700-dfbb-4c60-8110-e07b2b9ab83b
-- title:
--   Eigenvectors of the Fourier symbol of $-J_0\partial_t$
-- statement:
--   Let $\mu\in\mathbb{R}$, $m\in\mathbb{Z}$ and $c\in\mathbb{C}^{2n}$, and let $J_0$ be the standard complex structure on $\mathbb{R}^{2n}$ (regarded as a complex matrix). If
--   $$\mu\,c=-2\pi i m\,J_0 c,$$
--   then every component of $c$ satisfies $(\mu-2\pi m)(\mu+2\pi m)\,c_i=0$. In particular $c=0$ unless $\mu=\pm 2\pi m$.
--
--   Role: describes the eigenvalue equation of the Fourier symbol of the unperturbed asymptotic operator $A_0=-J_0\partial_t$ at frequency $m$; used to determine the spectrum and eigenspaces of $A_0$.
--
--   Formalization note: `J₀ n` is `Matrix.J` on `Fin n ⊕ Fin n` (from the Conley–Zehnder setting), mapped entrywise into `ℂ`; the frequency factor is written `((2 * Real.pi * m : ℝ) * Complex.I)` exactly as in `IsAsymptoticAction`.
-- source:
--   Standard Fourier-analysis fact; used for Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, §3.4, p. 63

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder Matrix

/-- If `c ∈ ℂ²ⁿ` solves `μ c = -2πim J₀ c` (the eigenvalue equation of the Fourier symbol of
`-J₀ ∂ₜ` at frequency `m`), then every component satisfies `(μ - 2πm)(μ + 2πm) cᵢ = 0`. -/
theorem symbol_eigen {n : ℕ} (μ : ℝ) (m : ℤ) (c : Fin n ⊕ Fin n → ℂ)
    (h : (μ : ℂ) • c = -((2 * Real.pi * m : ℝ) * Complex.I) •
      ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ c)) (i : Fin n ⊕ Fin n) :
    ((μ : ℂ) - ((2 * Real.pi * m : ℝ) : ℂ)) * ((μ : ℂ) + ((2 * Real.pi * m : ℝ) : ℂ)) * c i = 0 := by
  sorry

end AsymptoticOperator
