-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_proposition_4_2
-- name    : BipHamCount.Deterministic.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:49:13.004492+00:00
-- url     : https://prove2.me/theorems/7c0bcc44-1952-4f94-a70b-9a0fda416023
-- title:
--   Proposition 4.2 — small terms: exact output and entropy running time
-- statement:
--   Set $\alpha=60909/100000$ and $k=\lfloor\alpha m\rfloor$. There exist a constant $C>0$ and natural exponent $c$, independent of all inputs, such that for every side size $m$, zero–one matrices $A,B$ and left vertex $v$, the fixed smallTerms program returns $\sigma_{\le k}$ and, starting at zero cost, satisfies
--   $$\operatorname{cost}(\mathrm{smallTerms})\le C(m+1)^c\exp\big(mh(\alpha)\big)3^{\alpha m}.$$
--   Here $h$ is entropy in nats, and the exponent $\alpha m$ is real. Correctness and running time are simultaneous conclusions. This bounds the complete small-term contribution, including the middle layers.
--
--   Differences from the source:
--   - encoding: finite ordered vertex and side sets → finite types with linear orders, with Fin m as the zero-based ordered side; reason: every finite ordered set admits this relabelling; the minor factors use identical increasing orders
--   - encoding: A and B are the zero–one adjacency matrices from §2 p.4 → integer matrices with explicit ZeroOne hypotheses; reason: these hypotheses specify exactly the source matrices and prevent entry bit lengths from being unconstrained
--   - reading: k=αn/2 with α=0.60909 used as an integer index → α=60909/100000 and kOf m=floor(60909m/100000), where n=2m; reason: an integer threshold is required by the valid-set DP; floor preserves the exponential bounds up to polynomial factors, including finitely many small m
--   - encoding: binary entropy H in base two → Real.binEntropy in nats with exp replacing 2 raised to H; reason: exp(m·binEntropy x)=2^(m·H(x)), including x=0,1
--   - encoding: O-star suppresses a factor polynomial in n → positive C and natural c, both chosen before every input, and the factor C(m+1)^c; reason: n=2m; this expresses the same polynomial-factor bound and includes small sizes
--   - reading: time of the algorithm in §4 → charged bit operations of the fixed program; integer arithmetic costs (size|a|+size|b|+1)², with charged subset, table, loop and buffer operations; reason: the counter is generic; the reused Work definition supplies no unit-cost arithmetic assumption here; this accounts conservatively for integers of polynomial bit length
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Proposition 4.2, p. 7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Programs

open scoped BigOperators

namespace BipHamCount.Deterministic

/-- Proposition 4.2 pp.7–8: correctness AND bit-cost of the fixed small-term program.
The real exponent is αm; all constants precede every input. -/
theorem proposition_4_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ,
      ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ), ZeroOne A → ZeroOne B →
        ∀ v : Fin m,
          ((smallTerms m A B v (kOf m)).run 0).1 = sigmaSmall A B v (kOf m) ∧
          (((smallTerms m A B v (kOf m)).run 0).2 : ℝ) ≤
            C * ((m : ℝ)+1)^c * Real.exp (m*Real.binEntropy alpha) *
              (3 : ℝ)^(alpha*m) := by sorry

end BipHamCount.Deterministic
