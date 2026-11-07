-- Prove2me | Theorems.Thm_ApproxDegComp_eq_14
-- name    : ApproxDegComp.eq_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:31:44.737418+00:00
-- url     : https://prove2.me/theorems/1d30eafe-cbb8-4c6b-8cf3-28427d9e946c
-- title:
--   Eq. (14) — the squarefree terms of degree $\ge d_f$ of $\mathcal S(R)(z/\kappa)$ sum to at most $1/7$ when $KD\le d_f\kappa/(32e)$
-- statement:
--   Let $R:\mathbb R^n\to\mathbb R$ be a trigonometric polynomial of total frequency at most $D'$ with $|R|\le1$ on $\mathbb R^n$, let $\kappa>0$ and $d_f\ge1$, and assume
--
--   $$D'\le\frac{d_f\,\kappa}{32e}.$$
--
--   Then for every $z\in\{-1,1\}^n$
--
--   $$\Bigl|\mathcal S(R)\Bigl(\frac z\kappa\Bigr)-P(z)\Bigr|=\Bigl|\sum_{S\subseteq[n],\ |S|\ge d_f}\partial_SR(0)\prod_{i\in S}\frac{z_i}\kappa\Bigr|\le\sum_{r=d_f}^\infty8^{-r}\le\frac17,$$
--
--   where $P(z)=\sum_{r=0}^{d_f-1}\kappa^{-r}\mathcal S(H_r)(z)$ is the low-degree part of the squarefree extraction. In the proof of Theorem 23, $R$ is the trigonometric polynomial of Lemma 22 with $D'=KD$, $\kappa=2\lambda$ and $d_f=\widetilde{\deg}(f)$; the bound shows that if $\widetilde{\deg}(f\circ g)$ were too small, the polynomial $P$ of degree $<d_f$ would approximate $f$, a contradiction.
--
--   Differences from the source:
--   - generalization: the R, κ = 2λ, d_f = d̃eg(f) of the proof of Theorem 23 → every real trigonometric polynomial R of total frequency ≤ D′ with |R| ≤ 1, every κ > 0 and every d_f ≥ 1; reason: the step uses only these properties (via Lemmas 6 and 7); the proof's R, κ and d_f have them, so the statement specializes to the source's
--   - reading: |S(R)(z/κ) − P(z)| with P(z) = Σ_{r<d_f} κ^{−r} S(H_r)(z) → |Σ_{|S| ≥ d_f} ∂_S R(0) Π_{i∈S} z_i/κ|; reason: by Eq. (12) and the definition of P (p.23), S(R)(z/κ) − P(z) is exactly the sum of the squarefree terms of degree ≥ d_f
--   - encoding: KD (K a real constant, D = d̃eg(f∘g)) → D′ a natural number with R of total frequency ≤ D′; reason: total frequency is an integer; Lemma 22 gives total frequency ≤ deg Q ≤ KD, so one can take D′ = deg Q
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), proof of Theorem 23, Eq. (14), p.24 (P defined p.23, Eq. (12) p.23)

import Mathlib
import Definitions.Def_ApproxDegComp_sqfreeFun
import Definitions.Def_ApproxDegComp_HasTotalFreqLE
import Definitions.Def_ApproxDegComp_zOf

namespace ApproxDegComp

/-- **Eq. (14), proof of Theorem 23**, p.24.
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), proof of Theorem 23, pp.23–24: "Now, let P be a polynomial as follows:
P(z) = Σ_{r=0}^{d_f−1} κ^{−r} S(H_r)(z)." … "Let us assume that KD ≤ d_f κ/(32e). Then,
|S(R)(z/κ) − P(z)| ≤ Σ_{r=d_f}^∞ 8^{−r} ≤ 1/7. (14)"

Here `S(R)(z/κ) − P(z) = Σ_{r≥d_f} κ^{−r} S(H_r)(z)` is the part of the squarefree extraction
made of the monomials `Π_{i∈S} zᵢ/κ` with `|S| ≥ d_f` (Eq. (12)).

**Formalization Note** Stated for every real trigonometric polynomial `R` of total frequency at
most `D'` (the paper's `KD`, Lemma 22) with `|R| ≤ 1`, every `κ > 0` and every `d_f ≥ 1`;
the left side is written as the sum of the squarefree terms with `|S| ≥ d_f`. -/
theorem eq_14 (n D' df : ℕ) (R : (Fin n → ℝ) → ℝ) (hR : HasTotalFreqLE (fun θ => (R θ : ℂ)) D')
    (hb : ∀ θ, |R θ| ≤ 1) (κ : ℝ) (hκ : 0 < κ) (hdf : 1 ≤ df)
    (hD : (D' : ℝ) ≤ (df : ℝ) * κ / (32 * Real.exp 1)) :
    ∀ z : Fin n → Bool,
      |∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => df ≤ S.card),
          mixedPartial R S * ∏ i ∈ S, zOf (z i) / κ| ≤ 1 / 7 := by sorry

end ApproxDegComp
