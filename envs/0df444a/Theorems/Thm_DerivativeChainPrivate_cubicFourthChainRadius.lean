-- Prove2me | Theorems.Thm_DerivativeChainPrivate_cubicFourthChainRadius
-- name    : DerivativeChainPrivate.cubicFourthChainRadius
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T08:00:21.993011+00:00
-- url     : https://prove2.me/theorems/22a80464-cba6-471b-b154-2575c124c58c
-- title:
--   Complete chains for fourth powers of complex cubics
-- statement:
--   Let $q$ be a monic complex cubic with all its roots in a disk centered at $o\in\mathbb C$ of radius $R\ge0$. There exists a complete chain $z_1,\ldots,z_{12}$ for $q^4$ satisfying
--
--   $$D^{12-m}(q^4)(z_m)=0\quad(1\le m\le 12),\qquad
--   \sum_{m=1}^{11}|z_{m+1}-z_m|\le\frac{4\sqrt2}{3}R.$$
--
--   The first point is the centroid of the three roots of $q$, counted with multiplicity. All final 4 entries, from row 9 through row 12, coincide at one root of $q$. There are unit complex numbers $a,b$ with $\operatorname{Re}(a\overline b)=0$ such that both sequences $\operatorname{Re}(az_m)$ and $\operatorname{Re}(bz_m)$ are nondecreasing. They describe one common orthonormal coordinate frame, allowing reflection. Translation changes these coordinates only by constant offsets.
--
--   The statement includes repeated roots, zero radius, and degenerate centered coefficients. It assumes no supplied prefix, continuation theorem or genericity condition. The complete Lean proof has been accepted by Prove2me’s verifier. This restricted class theorem does not settle either unrestricted derivative-chain question.
-- source:
--   Fourth-power cubic derivative-chain research, H4_COMPLETE_CHAIN.md, Section 1, equations (1)–(2). https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fourth-md
--
--   Complete local Lean proof archive (193 files; predates final server packaging): https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/848808260c49b06b5abbdf5318325e6c72a8043e#file-formal-proofs-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.cubicFourthChainRadius (q : Polynomial ℂ) (hq : q.Monic) (hdeg : q.natDegree = 3)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x : ℂ, q.eval x = 0 → ‖x - o‖ ≤ R) :
    ∃ (z : Fin 12 → ℂ) (a b : ℂ),
      (∀ i, (derivative^[12 - (i.val + 1)] (q^4)).eval (z i) = 0) ∧
      z 0 = q.roots.sum / 3 ∧
      (∀ i : Fin 12, 8 ≤ i.val → z i = z 11) ∧ q.eval (z 11) = 0 ∧
      ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ (a * starRingEnd ℂ b).re = 0 ∧
      Monotone (fun i => (a * z i).re) ∧ Monotone (fun i => (b * z i).re) ∧
      chainCost z ≤ 4 * Real.sqrt 2 * R / 3 := by sorry
