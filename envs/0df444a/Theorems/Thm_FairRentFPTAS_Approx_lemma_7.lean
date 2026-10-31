-- Prove2me | Theorems.Thm_FairRentFPTAS_Approx_lemma_7
-- name    : FairRentFPTAS.Approx.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:50.122549+00:00
-- url     : https://prove2.me/theorems/1a4e39c6-7c0e-4594-8062-05365c537d7c
-- title:
--   Lemma 7, p. 17 — per-piece bounds for the rounded utility ((d), (e) on the open piece)
-- statement:
--   Let $\mathcal I$ be well formed and $0<\varepsilon<1$. Fix $a,r$ and a bounded piece $[x_1,x_2]$ of $v_a(r,\cdot)$ (after its zero $z^a_r$ has been made a break point) with slope magnitude $\lambda$, $H=v_a(r,x_1)$, $B=v_a(r,x_2)$ and $\bar\lambda=(1+\varepsilon)^{\lceil\log_{1+\varepsilon}\lambda\rceil}$. For all $x\in[x_1,x_2]$:
--
--   (a) $\bar v_a(r,x)\ge v_a(r,x)$;
--   (b) $B+\bar\lambda(x_2-x)\ge\bar v_a(r,x)$;
--   (c) $H-\frac{\bar\lambda}{1+\varepsilon}(x-x_1)\ge\bar v_a(r,x)$;
--
--   and for all $x\in(x_1,x_2)$:
--
--   (d) $\bar v_a(r,x)\ge0\iff H\ge0$ and $B\ge0$;
--   (e) $\bar v_a(r,x)\le0\iff H\le0$ and $B\le0$.
--
--   These are the inequalities used in both cases of the proof of Lemma 9.
--
--   **Formalization Note** The page states (d) and (e) on the closed piece; at an endpoint equal to $z^a_r$ the "only if" directions fail (for $v(x)=1-x$, the piece $[1,2]$ has $H=0$, $B=-1$ and $\bar v(1)=0\ge0$), so they are stated on the open piece.
-- source:
--   Arunachaleswaran, Barman & Rathi, Fully Polynomial-Time Approximation Schemes for Fair Rent Division, arXiv:1807.04163v1, p. 17, Lemma 7

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

namespace FairRentFPTAS.Approx

/-- Lemma 7, p. 17: for each bounded piece `[x₁, x₂]` (slope `λ`, `H = v(x₁)`, `B = v(x₂)`)
of `v_a(r, ·)` with its zero inserted as a break point, and `λ̄ = (1+ε)^⌈log_{1+ε} λ⌉`:
(a) `v̄ ≥ v`, (b) `B + λ̄ (x₂ − x) ≥ v̄`, (c) `H − λ̄/(1+ε) (x − x₁) ≥ v̄` on `[x₁, x₂]`, and
(d) `v̄ ≥ 0 ⇔ H ≥ 0 ∧ B ≥ 0`, (e) `v̄ ≤ 0 ⇔ H ≤ 0 ∧ B ≤ 0` on `(x₁, x₂)`. -/
theorem lemma_7 {n : ℕ} (I : Instance n) (ε : ℝ) (hI : Standing I) (hε : 0 < ε) (hε1 : ε < 1)
    (a r : Fin n) (e e' : ℝ × ℝ) (hpiece : [e, e'] <:+: (refineZero (I.v a r)).pieces) :
    (∀ x, e.1 ≤ x → x ≤ e'.1 →
      (I.v a r).eval x ≤ ((roundInst ε I).v a r).eval x ∧
      ((roundInst ε I).v a r).eval x ≤ (I.v a r).eval e'.1 + roundUp ε e.2 * (e'.1 - x) ∧
      ((roundInst ε I).v a r).eval x ≤ (I.v a r).eval e.1 - roundUp ε e.2 / (1 + ε) * (x - e.1)) ∧
    (∀ x, e.1 < x → x < e'.1 →
      (0 ≤ ((roundInst ε I).v a r).eval x ↔ 0 ≤ (I.v a r).eval e.1 ∧ 0 ≤ (I.v a r).eval e'.1) ∧
      (((roundInst ε I).v a r).eval x ≤ 0 ↔ (I.v a r).eval e.1 ≤ 0 ∧ (I.v a r).eval e'.1 ≤ 0)) := by sorry

end FairRentFPTAS.Approx
