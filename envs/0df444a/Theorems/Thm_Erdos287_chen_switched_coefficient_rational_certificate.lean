-- Prove2me | Theorems.Thm_Erdos287_chen_switched_coefficient_rational_certificate
-- name    : Erdos287.chen_switched_coefficient_rational_certificate
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T22:37:52.341115+00:00
-- url     : https://prove2.me/theorems/bffb76a6-9e54-505b-adc7-225a1e87137f
-- title:
--   Erdős 287 rational coefficient for the switched Chen sieve
-- statement:
--   For the three Chen sieve terms at level $5499/10000$, take the cutoffs $29/200$ and $183/800$ and the Buchstab cap $709/1250$. The stated rational expression bounds the numerical coefficient using 1024 right rectangles in each linear sieve term and seven terms of the odd-power logarithm series, with each rectangle rounded outwards. Its value is below $3587/1000$. The displayed comparisons give moment margins in periods $(3,8)$ and $(5,13)$ when the final coefficient is $897/250$.
-- source:
--   Erdős #287. Three Chen terms with mixed residue estimates at level 0.5499.

import Mathlib

theorem Erdos287.chen_switched_coefficient_rational_certificate :
    let θ : ℚ := 5499 / 10000
    let a : ℚ := 29 / 200
    let b : ℚ := 183 / 800
    let c : ℚ := 709 / 1250
    let d := (1 - b) / (2 + 1 / c)
    let dx := (θ / a - 3) / 1024
    let dt := (b - a) / 1024
    let scale : ℚ := 10 ^ 12
    let z (y : ℚ) := (y - 1) / (y + 1)
    let lowerLog (y : ℚ) :=
      2 * ∑ j ∈ Finset.range 7, z y ^ (2 * j + 1) / (2 * (j : ℚ) + 1)
    let upperLog (y : ℚ) :=
      lowerLog y + 2 * z y ^ 15 / (15 * (1 - (z y) ^ 2))
    let firstUpper :=
      2 / θ + (↑(∑ i ∈ Finset.range 1024,
        let x := 1 + ((i : ℚ) + 1) * dx
        ⌈scale * (2 / θ) * dx * upperLog x / (x + 1)⌉) : ℚ) / scale
    let secondLower :=
      (↑(∑ i ∈ Finset.range 1024,
        let t := a + ((i : ℚ) + 1) * dt
        ⌊scale * dt * lowerLog ((θ - t) / a - 1) / ((θ - t) * t)⌋) : ℚ) / scale
    let thirdUpper :=
      ((2 * c / a) * ((1 + a / b) * upperLog (b / a) - 2 * (1 - a / b)) +
        (1 + 2 * c) * upperLog (b / a) * (b - d) ^ 3 /
          (3 * (1 - 3 * b) * d ^ 3)) / (2 * θ)
    firstUpper - secondLower + thirdUpper < 3587 / 1000 ∧
    (897 / 250 : ℚ) + 1 / 13 < 11 / 3 ∧
    (897 / 250 : ℚ) + 1 / 100 < 18 / 5 := by sorry
