-- Prove2me | Theorems.Thm_DirTeleMC_lemma_B_5
-- name    : DirTeleMC.lemma_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:33:30.115209+00:00
-- url     : https://prove2.me/theorems/0a3d0cae-3dab-4a33-bc97-6201352d498d
-- title:
--   Lemma B.5 — the candidate chosen in one iteration of GREEDY is cheap
-- statement:
--   Let $\ell \ge 2$, $\eta = 2\ell - 1$, $b_h = (e-1)e^{(h-1)/\eta}$ and $\beta_h = h b_h$ for $1 \le h \le \eta$, and let $\Gamma > 0$ with $\Gamma \ge 4e(e-1)\eta\Lambda$.
--
--   **Lemma B.5.** $\beta_h < e(e-1)h$. Consider an iteration of the while loop of Algorithm 1 at a node $\sigma$ of height $1 \le h \le \eta$, with state $L_{\mathrm{cur}}$, residual set $R_{\mathrm{cur}}$ and residual demand $z_{\mathrm{cur}} \ge 1$. If some structure $Q$ rooted at $\sigma$ with maximum load at most $\Lambda$ covers $x \ge 1$ terminals of $R_{\mathrm{cur}}$, then some candidate has positive count, and every candidate $C$ that line 18 may choose satisfies
--   $$\Delta_{L_{\mathrm{cur}}}(C) \le \beta_h\, \mathrm{cnt}(C)\, \frac{c_{L_{\mathrm{cur}}}(Q)}{\bar x}, \qquad \bar x = \min\{x, z_{\mathrm{cur}}\}.$$
--
--   This is the density bound behind the logarithmic loss of greedy covering.
--
--   **Formalization Note** The iteration is given by its cheapest jumps and its recursive runs, exactly the data of a step of the run relation, so the lemma applies to every iteration of every run.
--
--   Differences from the source:
--   - generalization: residual set R_cur, a set of terminals of K → any finite vertex set R; reason: the residual sets of the algorithm are such sets; the statement does not use R ⊆ K
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Lemma B.5, p.27 (PDF p.28); proof pp.27–30 (PDF pp.28–31)

import Mathlib
import Definitions.Def_DirTeleMC_GreedyLoop

namespace DirTeleMC

/-- **Lemma B.5** (one iteration of GREEDY).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Lemma B.5, p.27: "Let b_h = (e − 1)e^{(h−1)/η} and β_h = h b_h for 1 ≤ h ≤ η, so that β_h < e(e − 1)h, and
suppose Γ ≥ 4e(e − 1)ηΛ. Consider an iteration of the while loop in line 3 of Algorithm 1 at a node σ of height
h ≥ 1, with state L_cur, residual set R_cur and residual demand z_cur ≥ 1. If some structure Q rooted at σ with
maximum load at most Λ covers x ≥ 1 terminals of R_cur, then some candidate has positive count, and the chosen
candidate C satisfies ∆_{L_cur}(C) ≤ β_h cnt(C) c_{L_cur}(Q)/x̄, x̄ = min{x, z_cur}."

For `ℓ ≥ 2`, `η = 2ℓ − 1`, a scale `Γ > 0` with `Γ ≥ 4e(e − 1)ηΛ`, and an iteration of the while loop of
Algorithm 1 at a node labelled `u` of height `1 ≤ h ≤ η`, with state `L`, residual set `R` and residual demand
`z ≥ 1` (the cheapest jumps `P` and recursive runs `out` of lines 5–13): `β_h < e(e − 1)h`; and if a structure
`Q` rooted at that node with maximum load at most `Λ` covers `x ≥ 1` vertices of `R`, then some candidate has
positive count, and every candidate `C` that line 18 may choose satisfies
`Δ_L(C) ≤ β_h · cnt(C) · c_L(Q) / min{x, z}`.

**Formalization Note.** `η = 2ℓ − 1` with `ℓ ≥ 2` is the standing setting of Appendix B (the proof uses
`η ≥ 3`). `x` is the number of vertices of `R` that `Q` covers. The iteration is given by its data
(`IterationData`), which are the premises of the constructors of `GreedyLoop`, so the lemma applies to every
iteration of every run. -/
theorem lemma_B_5 {n : ℕ} (adj : Fin n → Fin n → Bool) (θ ℓ : ℕ) (hℓ : 2 ≤ ℓ) (Γ Λ : ℝ) (hΓ : 0 < Γ)
    (hΓΛ : 4 * Real.exp 1 * (Real.exp 1 - 1) * ((2 * ℓ - 1 : ℕ) : ℝ) * Λ ≤ Γ)
    (u : Fin n) (h z : ℕ) (hh : 1 ≤ h) (hhη : h ≤ 2 * ℓ - 1) (hz : 1 ≤ z) (L : Fin n → ℕ)
    (R : Finset (Fin n)) (P : Fin n → List (Fin n)) (out : Fin n → List (JTree n))
    (hit : IterationData adj θ Γ u h z L R P out) :
    (h : ℝ) * ((Real.exp 1 - 1) * Real.exp (((h : ℝ) - 1) / ((2 * ℓ - 1 : ℕ) : ℝ))) <
        Real.exp 1 * (Real.exp 1 - 1) * h ∧
    ∀ Q : JTree n, JTree.IsStructure adj θ h Q → Q.label = u → (Q.maxLoad : ℝ) ≤ Λ →
      1 ≤ (R ∩ JTree.cov h Q).card →
      (∃ C ∈ candsOf u h (kids adj θ u) P out, 0 < cnt h R z C) ∧
      ∀ C, IsChosen Γ h z L R (candsOf u h (kids adj θ u) P out) C →
        incr Γ L C.loads ≤
          (h : ℝ) * ((Real.exp 1 - 1) * Real.exp (((h : ℝ) - 1) / ((2 * ℓ - 1 : ℕ) : ℝ))) *
            (cnt h R z C : ℝ) * lin Γ L Q.loads / (min (R ∩ JTree.cov h Q).card z : ℕ) := by sorry

end DirTeleMC
