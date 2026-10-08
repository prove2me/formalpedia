-- Prove2me | Theorems.Thm_CouplingHMC_Exact_eq_119_120
-- name    : CouplingHMC.Exact.eq_119_120
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:38.184039+00:00
-- url     : https://prove2.me/theorems/eafae947-cea0-451d-8074-1301c7921f03
-- title:
--   (119)–(120), p. 37 — max(1, aR₁)e^{−aR₁} f(r) ≤ r f′(r) for r > 0, and the chain ¼KT² max(1,aR₁)e^{−aR₁} > (1/20)KT²(1+ℛ/T)e^{−5ℛ/(2T)}
-- statement:
--   Let $T>0$, $\mathcal R\ge0$, $K>0$, $a=T^{-1}$, $R_1=\tfrac52(\mathcal R+T)$ and $f(r)=\int_0^r e^{-a\min(s,R_1)}ds$, so that $f'(r)=e^{-a\min(r,R_1)}$. Then
--
--   1. for every $r>0$,
--   $$\max(1,aR_1)\,e^{-aR_1}\,f(r)\le r\,e^{-a\min(r,R_1)}=r f'(r),$$
--   that is, $\inf_{r>0} rf'(r)/f(r)\ge\max(1,aR_1)e^{-aR_1}$;
--   2. $$\tfrac14KT^2\max(1,aR_1)e^{-aR_1}\ \ge\ \tfrac14KT^2\,\tfrac52\Bigl(1+\frac{\mathcal R}{T}\Bigr)e^{-5/2}e^{-\frac{5\mathcal R}{2T}}\ >\ \tfrac1{20}KT^2\Bigl(1+\frac{\mathcal R}{T}\Bigr)e^{-\frac{5\mathcal R}{2T}}.$$
--
--   These bound the contraction rate $c_1=\tfrac14KT^2\inf_{r>0}rf'(r)/f(r)$ of (119) from below, for pairs of points at distance at least $2\mathcal R$.
--
--   **Formalization Note.** The factor $\tfrac14$ is the one printed in (118)–(120).
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, §5, proof of Theorem 2.4, step (i), (119)–(120), p. 37

import Mathlib
import Definitions.Def_CouplingHMC_Exact_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace CouplingHMC.Exact

/-- (119)–(120), p. 37: with `a`, `R₁` of (29)–(30),
(a) `max(1, aR₁) e^{-aR₁} f(r) ≤ r f'(r)` for every `r > 0` (so `inf_{r>0} r f'(r)/f(r) ≥ max(1, aR₁) e^{-aR₁}`);
(b) `¼KT² max(1, aR₁) e^{-aR₁} ≥ ¼KT² (5/2)(1 + ℛ/T) e^{-5/2} e^{-5ℛ/(2T)} > (1/20)KT²(1 + ℛ/T) e^{-5ℛ/(2T)}`. -/
theorem eq_119_120 (K T ℛ : ℝ) (hT : 0 < T) (hℛ : 0 ≤ ℛ) (hK : 0 < K) :
    (∀ r : ℝ, 0 < r →
      max 1 (aC T * R1C T ℛ) * Real.exp (-(aC T * R1C T ℛ)) * fConc (aC T) (R1C T ℛ) r ≤
        r * Real.exp (-(aC T * min r (R1C T ℛ)))) ∧
    1 / 4 * K * T ^ 2 * (5 / 2) * (1 + ℛ / T) * Real.exp (-(5 / 2)) *
        Real.exp (-(5 * ℛ / (2 * T))) ≤
      1 / 4 * K * T ^ 2 * max 1 (aC T * R1C T ℛ) * Real.exp (-(aC T * R1C T ℛ)) ∧
    1 / 20 * K * T ^ 2 * (1 + ℛ / T) * Real.exp (-(5 * ℛ / (2 * T))) <
      1 / 4 * K * T ^ 2 * (5 / 2) * (1 + ℛ / T) * Real.exp (-(5 / 2)) *
        Real.exp (-(5 * ℛ / (2 * T))) := by sorry

end CouplingHMC.Exact
