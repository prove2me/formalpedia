-- Prove2me | Theorems.Thm_AsymptoticOperator_coeff_neg
-- name    : AsymptoticOperator.coeff_neg
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T22:48:13.889897+00:00
-- url     : https://prove2.me/theorems/663afc85-d05e-4dce-afa0-8bf1c458bf8b
-- title:
--   Fourier coefficients of a real $L^2$ loop are conjugate-symmetric
-- statement:
--   Let $f\in L^2(\mathbb{R}/\mathbb{Z},\mathbb{R}^{2n})$ (with the Haar probability measure) and let $\hat f_k=\int_{\mathbb{R}/\mathbb{Z}} e^{-2\pi i k t} f(t)\,dt\in\mathbb{C}^{2n}$ be its Fourier coefficients, computed componentwise on the complexification. Then for every $k\in\mathbb{Z}$ and every coordinate $i$,
--   $$(\hat f_{-k})_i=\overline{(\hat f_k)_i}.$$
--
--   Role: the reality condition on Fourier coefficients of real loops, used throughout the spectral theory of the asymptotic operators $A_S=-J_0\partial_t-S$.
--
--   Formalization note: `L2 n`, `coeff` are from `Definitions.Def_AsymptoticOperator_Setting`; coordinates are indexed by `Fin n ⊕ Fin n`; complex conjugation is `starRingEnd ℂ`.
-- source:
--   Standard Fourier-analysis fact; used for Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, §3.4, p. 63

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- The Fourier coefficients of a real `L²` function on the circle are conjugate-symmetric:
`f̂₋ₖ = conj f̂ₖ` componentwise. -/
theorem coeff_neg {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f (-k) i = (starRingEnd ℂ) (coeff f k i) := by sorry

end AsymptoticOperator
