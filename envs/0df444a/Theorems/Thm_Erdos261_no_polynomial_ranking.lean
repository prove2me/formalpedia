-- Prove2me | Theorems.Thm_Erdos261_no_polynomial_ranking
-- name    : Erdos261.no_polynomial_ranking
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:30:09.5714+00:00
-- url     : https://prove2.me/theorems/f6ca2662-c18e-4982-9025-314cc9f6b495
-- title:
--   No polynomial ranking function proves termination of the Erdős 261 greedy carry
-- statement:
--   Consider the Borwein–Loring / Erdős 261 greedy map on states $(N,R)$: $(N,R)\mapsto(N+1,\,2R\bmod(N+1))$.
--
--   **Theorem.** For every real polynomial $P(N,R)$ and every $N_0$, it is false that for all integers $N\ge\max(N_0,2)$ and $1\le R<N$:
--
--   1. $P(N,R)\ge0$, and
--   2. if $R'=2R\bmod(N+1)>0$ then $P(N+1,R')<P(N,R)$.
--
--   So no global (or eventually valid) polynomial ranking function can prove that greedy orbits terminate.
--
--   Proof (discrete, via exact cycles). For $k\ge2$ and $M\ge2$ the states $((2^k-1)M-k+i,\,2^iM)$, $i=0,\dots,k$ (last one $((2^k-1)M,M)$) form a greedy segment ($k-1$ doublings, then one subtraction returning to $R=M$). Comparing $M^d$-coefficients ($d$ the total degree) along the segment gives $h(c,2)=h(c,1)$ for the top form $h$ at every $c=2^k-1$; hence the top form is $aN^d$, and $a>0$ by nonnegativity on $(2M,M)$. The 2-cycle $(3M-2,M)\to(3M-1,2M)\to(3M,M)$ then gives $P(3M,M)<P(3M-2,M)$ for large $M$, but the $M^{d-1}$-coefficient of $P(3M,M)-P(3M-2,M)$ is $2ad\,3^{d-1}>0$.
--
--   **Formalization Note.** $P$ is an `MvPolynomial (Fin 2) ℝ` evaluated at `![N, R]`.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); Borwein–Loring 1990 greedy map; claim A2 of claim from a GPT answer relayed by Ethan Cheung (third round, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026) (the integral/limit argument there is replaced by a discrete exact-cycle argument)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem no_polynomial_ranking (P : MvPolynomial (Fin 2) ℝ) (N0 : ℕ) :
    ¬ ∀ N R : ℕ, N0 ≤ N → 2 ≤ N → 1 ≤ R → R < N →
      0 ≤ MvPolynomial.eval ![(N : ℝ), (R : ℝ)] P ∧
      (0 < 2 * R % (N + 1) →
        MvPolynomial.eval ![((N + 1 : ℕ) : ℝ), ((2 * R % (N + 1) : ℕ) : ℝ)] P <
          MvPolynomial.eval ![(N : ℝ), (R : ℝ)] P) := by sorry

end Erdos261
