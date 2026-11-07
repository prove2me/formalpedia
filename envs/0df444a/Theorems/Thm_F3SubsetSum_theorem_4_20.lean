-- Prove2me | Theorems.Thm_F3SubsetSum_theorem_4_20
-- name    : F3SubsetSum.theorem_4_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:31:11.550303+00:00
-- url     : https://prove2.me/theorems/b52e39c7-abed-42b8-9a9f-38ff79eeee42
-- title:
--   Theorem 4.20 — $\bar\rho(W)\ge(\dim W/3)^{1-2/D}$
-- statement:
--   Let $q\ge3$ be prime, $D\ge3$, and $W\subseteq\overline R{}_D^*$ a nonzero subspace, where $\overline R_D$ is the degree-$D$ part of $\overline{\mathbb F}_q[x_1,\dots,x_n]/(x_1^q,\dots,x_n^q)$. Then
--
--   $$\bar\rho(W)\ge\Bigl(\frac{\dim W}{3}\Bigr)^{1-2/D}.$$
--
--   The symbolic rank is thus bounded below by the dimension alone; with Lemma 4.15 this gives the drift $\gamma(h)=(h/3)^{1-2/D}$ of Proposition 4.13.
--
--   Differences from the source: none.
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Theorem 4.20, p.28 (proof pp.28–29)

import Mathlib
import Definitions.Def_F3SubsetSum_TruncatedRing
import Definitions.Def_F3SubsetSum_SymbolicRank

namespace F3SubsetSum

/-- **Theorem 4.20** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, Theorem 4.20,
p.28; proof pp.28–29): "For D ≥ 3, every nonzero subspace W ⊆ R̄*_D satisfies
ρ̄(W) ≥ (dim(W)/3)^{1−2/D}."

Here `q ≥ 3` is prime, `R̄_D` is the degree-`D` part of `F̄_q[x_1, …, x_n]/(x_1^q, …, x_n^q)` over
the algebraic closure `F̄_q` (p.26), `R̄*_D` its dual, and `ρ̄(W)` the rank of the generic
contraction `C_{L_z}|_W` over `F̄_q(z_1, …, z_n)` (eq. (46)).

**Formalization Note** The power is a real power. -/
theorem theorem_4_20 (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n D : ℕ) (hD : 3 ≤ D)
    (W : Submodule (AlgebraicClosure (ZMod q))
      (Module.Dual (AlgebraicClosure (ZMod q)) (Rd (AlgebraicClosure (ZMod q)) n q D)))
    (hW : W ≠ ⊥) :
    ((Module.finrank (AlgebraicClosure (ZMod q)) W : ℝ) / 3) ^ (1 - 2 / (D : ℝ)) ≤
      symbolicRank (AlgebraicClosure (ZMod q)) n q D W := by sorry

end F3SubsetSum
