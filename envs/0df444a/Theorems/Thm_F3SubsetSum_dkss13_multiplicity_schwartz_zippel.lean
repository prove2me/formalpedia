-- Prove2me | Theorems.Thm_F3SubsetSum_dkss13_multiplicity_schwartz_zippel
-- name    : F3SubsetSum.dkss13_multiplicity_schwartz_zippel
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:13.024247+00:00
-- url     : https://prove2.me/theorems/d5c189e2-04b2-4f38-9d25-590e6ef781e5
-- title:
--   Eq. (44), [DKSS13] — multiplicity Schwartz–Zippel: $\mathbb E_a[\mathrm{mult}_a(p)]\le\deg(p)/q$
-- statement:
--   Let $q\ge3$ be prime and $p\in\mathbb F_q[z_1,\dots,z_n]$ nonzero. For $a$ uniform in $\mathbb F_q^n$,
--
--   $$\mathbb E_a\bigl[\mathrm{mult}_a(p)\bigr]\le\frac{\deg(p)}{q},$$
--
--   where $\mathrm{mult}_a(p)$ is the least total degree of a nonzero monomial of $p(z+a)$ and $\deg$ is the total degree. This is the lemma of Dvir, Kopparty, Saraf and Sudan (2013), cited in the proof of Lemma 4.15 and applied there to a nonzero minor of the generic contraction.
--
--   Differences from the source: none.
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, proof of Lemma 4.15, eq. (44), p.25 (cited: Dvir, Kopparty, Saraf, Sudan 2013)

import Mathlib
import Definitions.Def_F3SubsetSum_RootMultiplicity

namespace F3SubsetSum

/-- **The multiplicity Schwartz–Zippel lemma [DKSS13]** as used in the proof of Lemma 4.15
(Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, proof of Lemma 4.15, eq. (44),
p.25): "For an n-variate nonzero polynomial p(z) over the base field F_q and a ∈ F_q^n, we use
mult_a(p(z)) to denote the multiplicity of the root z = a. … The multiplicity Schwartz-Zippel
lemma [DKSS13] gives E_a[mult_a(p(z))] ≤ deg(p)/q."

For `q ≥ 3` prime (as in Problem 1.5) and every nonzero `p ∈ F_q[z_1, …, z_n]`, the average of
`mult_a(p)` over `a ∈ F_qⁿ` is at most `deg(p)/q`, where `deg` is the total degree.

**Formalization Note** A cited result (Dvir, Kopparty, Saraf, Sudan 2013), not proved in the
paper. -/
theorem dkss13_multiplicity_schwartz_zippel (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n : ℕ)
    (p : MvPolynomial (Fin n) (ZMod q)) (hp : p ≠ 0) :
    (∑ a : Fin n → ZMod q, (rootMult a p : ℝ)) / (q : ℝ) ^ n ≤ (p.totalDegree : ℝ) / q := by sorry

end F3SubsetSum
