-- Prove2me | Theorems.Thm_DetDLP_primitive_root_scan_correctness
-- name    : DetDLP.primitive_root_scan_correctness
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T11:52:43.758772+00:00
-- url     : https://prove2.me/theorems/09e922b6-45af-445d-abce-1715c1a3e089
-- title:
--   Deterministic Factor-Base Scan and Primitive-Root Construction Correctness
-- statement:
--   For any prime $p$ and factor-base lists $F : \mathrm{Fin}\,m \to \mathrm{List}\,(\mathbb{Z}/p\mathbb{Z})^*$ whose blocks contain at least one $\pi$-th non-residue for each prime $\pi \mid (p-1)$, scanning $U = \mathrm{flatten}(\mathrm{ofFn}\,F)$ via `U.find?` recovers valid witnesses $a_\pi$ with $a_\pi^{(p-1)/\pi} \neq 1$, outputs $h = \prod_{\pi \mid p-1} a_\pi^{(p-1)/\pi^{v_\pi(p-1)}}$ of exact order $p-1$, and performs at most $b \sum_i |F_i|$ prime-power tests since $\omega(p-1) \le \lceil \log_2 p \rceil$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.3, Proof of Proposition 3.3 (pp. 10–11)

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

/-- Deterministic scan correctness and complexity count for Proposition 3.3 (Section 3.3):
given a prime `p` and factor-base lists `F : Fin m → List (ZMod p)ˣ` containing at least one
`π`-th non-residue witness for every prime divisor `π ∣ (p - 1)`, scanning `U = (List.ofFn F).flatten`
with `U.find?` recovers valid witnesses `a π`, constructs a primitive root `h` modulo `p`
(`orderOf h = p - 1`), and scans at most `bitLen p * ∑ i, (F i).length` pairs `(π, u)`. -/
theorem primitive_root_scan_correctness :
    ∀ (p m : ℕ) [Fact p.Prime] (F : Fin m → List (ZMod p)ˣ),
      (∀ π ∈ (p - 1).primeFactors, ∃ i : Fin m, ∃ u ∈ F i, u ^ ((p - 1) / π) ≠ 1) →
      let U : List (ZMod p)ˣ := (List.ofFn F).flatten
      let a : ℕ → (ZMod p)ˣ := fun π =>
        (U.find? (fun u => decide (u ^ ((p - 1) / π) ≠ 1))).getD 1
      let h : (ZMod p)ˣ :=
        ∏ π ∈ (p - 1).primeFactors,
          (a π) ^ ((p - 1) / π ^ (p - 1).factorization π)
      (∀ π ∈ (p - 1).primeFactors, (a π) ^ ((p - 1) / π) ≠ 1) ∧
      orderOf h = p - 1 ∧
      (p - 1).primeFactors.card ≤ bitLen p ∧
      (p - 1).primeFactors.card * U.length ≤ bitLen p * (∑ i : Fin m, (F i).length) := by sorry

end DetDLP
