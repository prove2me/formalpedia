-- Prove2me | Theorems.Thm_ChatterjeeQFT_electronWeight_intertwine
-- name    : ChatterjeeQFT.electronWeight_intertwine
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:41:44.988065+00:00
-- url     : https://prove2.me/theorems/868d8ae8-3b07-45d1-8ad3-974c246a15b0
-- title:
--   Lemma 25.1: $A^{\dagger} V_{\kappa(A)p}^{-2} A = V_p^{-2}$
-- statement:
--   This is Lemma 25.1 of the source, stated directly in terms of an element
--   $A \in SL(2,\mathbb{C})$ rather than of a section $\varrho$ of the covering map: for every
--   $A \in SL(2,\mathbb{C})$ and every $p \in X_m$,
--
--   $$A^{\dagger}\, V_{\kappa(A)p}^{-2}\, A \;=\; V_p^{-2},$$
--
--   where $\kappa(A)$ is the Lorentz transformation induced by $A$ and $V_q$ is the pure boost taking
--   $p^*$ to $q$. Since $\varrho(A) = \pm A$ for a section $\varrho$ and the expression is quadratic in
--   $A$, this is equivalent to the form in the lecture notes. It is the algebraic identity that makes
--   the electron inner product invariant, and hence the spinor representation unitary.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 25 §25.3, Lemma 25.1, p. 109 ("For any $A$ and $p$, $\varrho(A)^{\dagger} V_{Ap}^{-2}\varrho(A) = V_p^{-2}$").

import Mathlib
import Definitions.Def_ChatterjeeQFT_ElectronSpace
open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

namespace ChatterjeeQFT

theorem electronWeight_intertwine (m : ℝ) (hm : 0 < m) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.det = 1) (p : Fin 4 → ℝ) (hp : p ∈ massShell m) :
    Aᴴ * electronWeight m (kappa A p) * A = electronWeight m p := by sorry

end ChatterjeeQFT
