-- Prove2me | Theorems.Thm_ExactDFTRefine_Main_separated_P16A8Z_fourier_transfer
-- name    : ExactDFTRefine.Main.separated_P16A8Z_fourier_transfer
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:09:57.193825+00:00
-- url     : https://prove2.me/theorems/11a9526f-d2bb-435a-bc94-7c48ba40785c
-- title:
--   External P16A8Z recursion and Fourier transfer at every saving $0<\kappa<C$
-- statement:
--   This is the external circuit/recursion/Fourier-reduction step used in the proof of Theorem 1.1. Let $C = 60403319/20000000000$ and $t = 1-C$. Consider the completed and split P16A8Z tensor unit at tensor power $v=11640$, maximum charged-block rank $J=20^v$, and minimum target rank $B=21^v$. Suppose that its moments satisfy the strict comparison $M_t(P')<M_t(T')$ and that every charged-block rank is strictly smaller than every target rank.
--
--   Then, for every fixed real saving $0<\kappa<C$, there are fixed deterministic programs $P_1$ and $P_2$ in the exact complex-arithmetic RAM model, a natural integer-bound exponent $c$, a real constant $K>0$, and a threshold $n_0$ such that for every length $n\ge1$ and every input $x\in\mathbb C^n$, the two-program run computes $\mathrm{DFT}_n x$. The run includes one supplied root, has root order $1\le D(n)<1024n^3$, keeps every integer value and address at most $(n+2)^c$ in absolute value, and for $n\ge n_0$ its total work $W$ satisfies
--   $$
--   W\le K\,n\,(\log n)^{1-\kappa}(\log\log n)^2.
--   $$
--
--   Kartal's P16A8Z circuit and tensor construction realize the completed and split rank multisets. The moment comparison and rank separation are the inputs to Sussman's mixed-target recursion, which supplies the kernel at every exponent strictly above $1-C$. OpenAI's Fourier reduction, including scalar preparation and the uniform root-order and integer bounds, turns that kernel into the fixed programs and incurs the displayed $(\log\log n)^2$ overhead.
--
--   **Formalization Note.** This theorem is the explicit external-artifact boundary of the present paper: these circuit, recursion, and reduction arguments are cited rather than reproved from the finite moment arithmetic in §§3–4. The predicate `DFTRun` contains the exact DFT correctness, supplied-root, root-order, instruction-count, and polynomial integer-bound requirements.
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 6, proof of Theorem 1.1, first paragraph (P16A8Z circuit, tensor realization, Sussman mixed-target recursion at any exponent strictly above 1-C) and second paragraph (Fourier reduction with (log log n)^2 overhead). External inputs: Kartal [9], pinned snapshot 859d6949ef4bdcab4ba661d09cd7fd720d0c4960; Sussman [12], wht-power-saving-lean; OpenAI [11], An explicit power saving for the exact discrete Fourier transform.

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_RAM
import Definitions.Def_ExactDFTRefine_Main_Moments
open ExactDFTRefine.Main

/-- Conditional external transfer at the p. 6 seam: the completed and split
P16A8Z tensor unit at v = 11640, with the Proposition 4.2 hypotheses, yields
fixed exact-RAM DFT programs at every saving below C. -/
theorem ExactDFTRefine.Main.separated_P16A8Z_fourier_transfer
    (κ : ℝ) (hκ0 : 0 < κ) (hκC : κ < Cpar)
    (hmoment :
      moment tpar (Pprime blocksP targetsT 11640 (20 ^ 11640) (21 ^ 11640)) <
        moment tpar (Tprime targetsT 11640 (21 ^ 11640)))
    (hsep :
      ∀ p ∈ Pprime blocksP targetsT 11640 (20 ^ 11640) (21 ^ 11640),
        ∀ q ∈ Tprime targetsT 11640 (21 ^ 11640), p < q) :
    ∃ (P₁ P₂ : Program) (c : ℕ) (K : ℝ) (n₀ : ℕ), 0 < K ∧
      ∀ n : ℕ, 1 ≤ n → ∀ x : Fin n → ℂ, ∃ W : ℕ, DFTRun P₁ P₂ c n x W ∧
        (n₀ ≤ n → (W : ℝ) ≤
          K * n * Real.log (n : ℝ) ^ (1 - κ) * Real.log (Real.log (n : ℝ)) ^ 2) := by sorry
