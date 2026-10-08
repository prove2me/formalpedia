-- Prove2me | Theorems.Thm_DiaconisStroock_OddPaths_inner_self_le_iota_mul
-- name    : DiaconisStroock.OddPaths.inner_self_le_iota_mul
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:06:48.346297+00:00
-- url     : https://prove2.me/theorems/822a4f90-ea53-41c0-9a15-d0618788bdac
-- title:
--   §1C, proof of Proposition 2, pp. 40–41 — E(φ²) ≤ (ι/2)(E(φ²) + ⟨φ, Pφ⟩_π)
-- statement:
--   Let $P$ be an irreducible transition matrix on a finite set $X$, reversible with respect to its stationary distribution $\pi$, and $Q(x,y)=\pi(x)P(x,y)$. Let $\Sigma=(\sigma_x)_{x\in X}$ be a system of odd closed paths (each $\sigma_x$ runs from $x$ to $x$ along edges with $Q>0$, has an odd number of edges and traverses no directed edge twice), and let $\iota=\iota(\Sigma)$ be the quantity (1.7). Then for every $\varphi:X\to\mathbb R$,
--
--   $$
--   E(\varphi^2)\le\frac{\iota}{2}\Big(E(\varphi^2)+\langle\varphi,P\varphi\rangle_{L^2(\pi)}\Big),
--   $$
--
--   where $E(\varphi^2)=\sum_x\varphi(x)^2\pi(x)$ and $\langle\varphi,P\varphi\rangle_{L^2(\pi)}=\sum_x\varphi(x)(P\varphi)(x)\pi(x)$.
--
--   This is the Poincaré-type inequality for the operator $I+P$ that yields Proposition 2: applied to an eigenfunction it bounds the eigenvalue from below.
--
--   **Formalization Note** Aperiodicity, a hypothesis of Proposition 2, is not assumed: once a system of odd paths is given, the inequality holds without it (and the existence of such a system forces it).
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), pp. 40–41, §1C, proof of Proposition 2 (the displayed chain of inequalities), https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_DiaconisStroock_OddPaths_Iota
open MarkovMixing

namespace DiaconisStroock.OddPaths

theorem inner_self_le_iota_mul {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ)
    (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π)
    (hrev : DetailedBalance P π) (S : V → List V) (hS : IsOddPathSystem P π S) :
    ∀ φ : V → ℝ,
      innerPi π φ φ ≤ iota P π S / 2 * (innerPi π φ φ + innerPi π φ (P.mulVec φ)) := by sorry

end DiaconisStroock.OddPaths
