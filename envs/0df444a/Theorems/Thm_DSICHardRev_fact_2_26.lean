-- Prove2me | Theorems.Thm_DSICHardRev_fact_2_26
-- name    : DSICHardRev.fact_2_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:40.914716+00:00
-- url     : https://prove2.me/theorems/64ff7065-e3b2-4d99-821e-393e5c251637
-- title:
--   Fact 2.26 — Pinsker's inequality, conditional form
-- statement:
--   For random variables $X,Y,Z$ with finite ranges,
--   $$\mathbb E\Big[\mathrm{TV}\big(\mathrm{Law}(X\mid Y,Z),\,\mathrm{Law}(X\mid Z)\big)^2\Big]\;\le\;\frac{\ln 2}{2}\,\mathbb I(X;Y\mid Z),$$
--   where the expectation is over $(Y,Z)$, $\ln$ is the natural logarithm and $\mathbb I$ is measured in bits.
--
--   It converts the information bound of Lemma 3.8 into a bound on how far conditional laws move.
--
--   Differences from the source:
--   - reading: discrete random variables → random variables with finite ranges on a finite probability space; reason: Definition 2.22's bound log|X| presupposes finite ranges and every variable the paper uses is finite; the quantities depend only on the joint law
--   - encoding: the expectation over (Y, Z) → ∑ over values (y, z) weighted by Pr[(Y, Z) = (y, z)]; reason: values of probability 0 carry weight 0, where Law(X | Y = y, Z = z) is undefined
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §2.5, p.11, Fact 2.26

import Mathlib
import Definitions.Def_DSICHardRev_Information

namespace DSICHardRev

/-- **Fact 2.26 (Pinsker's Inequality)** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §2.5, p.11):
for discrete random variables `X, Y, Z`,
`E[TV(Law(X | Y, Z), Law(X | Z))²] ≤ (ln 2 / 2) 𝕀(X ; Y | Z)`.

**Formalization Note.** Finite ranges on a finite probability space `P`. The expectation is over
`(Y, Z)`; values of probability `0` carry weight `0`. `ln` is the natural logarithm and `𝕀` is in
bits. -/
theorem fact_2_26 {Ω α β γ : Type} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]
    (P : FinProb Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    P.expectOver (fun ω => (Y ω, Z ω))
        (fun yz => tv (P.condLaw X (fun ω => (Y ω, Z ω)) yz) (P.condLaw X Z yz.2) ^ 2) ≤
      Real.log 2 / 2 * P.mutualInfo X Y Z := by sorry

end DSICHardRev
