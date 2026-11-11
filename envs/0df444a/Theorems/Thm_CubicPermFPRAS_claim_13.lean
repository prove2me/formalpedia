-- Prove2me | Theorems.Thm_CubicPermFPRAS_claim_13
-- name    : CubicPermFPRAS.claim_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:46.558534+00:00
-- url     : https://prove2.me/theorems/6b789e12-f590-4820-a6ef-182461d22504
-- title:
--   Claim 13, p.14 — the assignment Glauber dynamics is irreducible with stationary distribution $\nu_a$
-- statement:
--   Let $B$ be an $n\times n$ matrix with positive entries and rows summing to $1$, $J\ge0$ and $a>0$. The assignment Glauber dynamics with positive Laplacian $L_a$ of Eq. (14) is irreducible: every assignment can be reached from every other along moves of positive rate. Its stationary distribution is $\nu_a$: $\nu_aL_a=0$.
--
--   Differences from the source:
--   - generalization: the rescaled matrix $B$ of Eq. (10) and $J=J_\alpha n^2$ → every matrix $B$ with positive entries and rows summing to $1$, and every $J\ge0$; reason: the rescaled matrix is such a matrix; the proofs (§8.2–8.3) use only these properties
--   - encoding: irreducible; stationary distribution → reachability along negative off-diagonal entries of $L_a$; $\nu_aL_a=0$; reason: the standard meanings for a continuous-time chain given by its Laplacian
--   - encoding: an $n\times n$ instance ($V_1$, $V_2$ of size $n$) → the hypothesis $1\le n$; reason: the paper's vertex classes $V_1,V_2$ are nonempty throughout (an anchor $r\in V_1$ exists); $n=0$ is no instance of the source
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Claim 13, p.14 (PDF 16); proof in §8.3 (PDF 51–52)

import Mathlib
import Definitions.Def_CubicPermFPRAS_nuAux

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Claim 13**, p.14 (PDF 16), X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…); proved in §8.3 (p.49–50).

The assignment Glauber dynamics is irreducible and has stationary distribution `ν_a`.

**Formalization Note.** The dynamics is the continuous-time chain with positive Laplacian
`L_a` of Eq. (14): irreducibility is reachability of every configuration from every other
along moves of positive rate (negative off-diagonal entries of `L_a`), and stationarity is
`ν_a L_a = 0`. Stated for every `a > 0`, every matrix `B` with positive entries and rows
summing to `1` (the rescaled matrix of Eq. (10) is such a matrix) and every `J ≥ 0` (the paper
fixes `J = J_α n²`). -/
theorem claim_13 (n : ℕ) (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) (hB : ∀ u v, 0 < B u v)
    (hrow : ∀ u, ∑ v, B u v = 1) (J : ℝ) (hJ : 0 ≤ J) (a : ℝ) (ha : 0 < a) :
    (∀ σ τ : Asg n, Relation.ReflTransGen (fun x y => glauberLap B J a x y < 0) σ τ) ∧
      Matrix.vecMul (nuAux B J a) (glauberLap B J a) = 0 := by sorry

end CubicPermFPRAS
