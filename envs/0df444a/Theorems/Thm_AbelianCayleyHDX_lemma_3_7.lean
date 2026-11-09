-- Prove2me | Theorems.Thm_AbelianCayleyHDX_lemma_3_7
-- name    : AbelianCayleyHDX.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:40:06.160205+00:00
-- url     : https://prove2.me/theorems/dba34c7a-757e-425f-8e01-79b21d1cfad1
-- title:
--   Lemma 3.7 — the column graph is connected and $\mathrm{Spec}(P_D|_{\mathbf 1^\perp})$ is in Eq. (3.2)
-- statement:
--   Under the standing assumptions of Section 3 ($q = 2^h \ge 8$, $F = \mathbb F_{q^2}$, $t \ge 1$, $D \subseteq \mathrm{PG}(t-1,F)$ spanning, $\hat\nu = |\hat D|$, $\Delta = \Delta(D)$), the graph of Lemma 3.5 is connected, and its normalized adjacency operator $P_D$ satisfies
--   $$\mathrm{Spec}\big(P_D|_{\mathbf 1^\perp}\big) \subseteq \Big[-\frac{1}{q^2 - 2},\ \max\Big\{1 - \frac{q^2\Delta}{\hat\nu},\ \frac{1}{(q^2-2)(q^2-1)}\Big\}\Big]. \qquad (3.2)$$
--   That is, every eigenvalue $\mu$ of $P_D$ with an eigenvector $f \ne 0$ satisfying $\sum_c f(c) = 0$ lies in this interval.
--
--   Differences from the source:
--   - encoding: $F = \mathbb F_{q^2}$ → any finite field with $q^2$ elements; reason: all such fields are isomorphic to $\mathbb F_{q^2}$
--   - encoding: $q = 2^h \ge 8$ → $h \in \mathbb N$ with $8 \le 2^h$; reason: same parameters
--   - encoding: $\mathrm{Spec}(P_D|_{\mathbf 1^\perp})$ → the eigenvalues of $P_D$ having a nonzero eigenvector with coordinate sum $0$; reason: $P_D$ is real symmetric and fixes the constants, so $\mathbf 1^\perp$ is invariant and these are the eigenvalues of the restriction
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 3.7, p.13, Eq. (3.2)

import Mathlib
import Definitions.Def_AbelianCayleyHDX_IsSpanning
import Definitions.Def_AbelianCayleyHDX_Delta
import Definitions.Def_AbelianCayleyHDX_colGraph
import Definitions.Def_AbelianCayleyHDX_PD

namespace AbelianCayleyHDX

/-- **Lemma 3.7** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 3.7, p.13, Eq. (3.2)). Under the standing assumptions of Section 3
(`q = 2^h ≥ 8`, `F = 𝔽_{q²}`, `t ≥ 1`, `D ⊆ PG(t − 1, F)` spanning, `ν̂ = |D̂|`, `Δ = Δ(D)`), the
graph of Lemma 3.5 is connected, and
$$\mathrm{Spec}(P_D|_{1^\perp}) \subseteq \Big[-\tfrac{1}{q^2-2},\ \max\Big\{1 - \tfrac{q^2\Delta}{\hat\nu},\ \tfrac{1}{(q^2-2)(q^2-1)}\Big\}\Big].$$

**Formalization Note** `P_D` is real symmetric and fixes the constants, so `1^⊥` is invariant and
the spectrum of the restriction is the set of eigenvalues `μ` having an eigenvector `f ≠ 0` with
`∑ f = 0`; the statement is in that form. -/
theorem lemma_3_7 (h : ℕ) (hq : 8 ≤ 2 ^ h) {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = (2 ^ h) ^ 2) {t : ℕ} (ht : 1 ≤ t) (D : Finset (PG t F))
    (hD : IsSpanning D) :
    (colGraph D).Connected ∧
    ∀ (μ : ℝ) (f : Omega F t → ℝ), f ≠ 0 → ∑ c, f c = 0 → (PD D).mulVec f = μ • f →
      -1 / (((2 : ℝ) ^ h) ^ 2 - 2) ≤ μ ∧
      μ ≤ max (1 - ((2 : ℝ) ^ h) ^ 2 * (Delta D : ℝ) / ((Dhat D).card : ℝ))
        (1 / ((((2 : ℝ) ^ h) ^ 2 - 2) * (((2 : ℝ) ^ h) ^ 2 - 1))) := by sorry

end AbelianCayleyHDX
