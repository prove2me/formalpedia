-- Prove2me | Theorems.Thm_Arxiv2610_39302_k_pairs_identify_rotation
-- name    : Arxiv2610_39302.k_pairs_identify_rotation
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T03:02:10.295977+00:00
-- url     : https://prove2.me/theorems/39ee8d45-7267-4cca-88b4-fe976a677a52
-- title:
--   Proposition 2: $k$ pairs identify the rotation
-- statement:
--   Work in the setting of Theorem 1 and Proposition 1: a finite world with $p>0$, a positive-pair law $\pi$ with marginals $p$, $1\le k<|Z|$, $\mu_k>\mu_{k+1}$ (with $\mu_{|Z|}:=-\infty$), two modalities with injective renderings $g_1,g_2$, and minimisers $f_1^\star,f_2^\star$ of their spectral objectives.
--
--   1. Every rotation of a whitened embedding is whitened: if $E_ph=0$ and $E_phh^\top=I_k$, then $E_p(Rh)=0$ and $E_p(Rh)(Rh)^\top=I_k$ for every $R\in O(k)$.
--   2. Let $Q\in O(k)$ satisfy $f_1^\star\circ g_1=Q\,f_2^\star\circ g_2$. If the embeddings $f_2^\star(g_2(z_1)),\dots,f_2^\star(g_2(z_n))$ of $n\ge k$ world states span $\mathbb{R}^k$, then $Q$ is the unique minimiser over $R\in O(k)$ of
--   $$\sum_{i\le n}\big\|f_1^\star(g_1(z_i))-R\,f_2^\star(g_2(z_i))\big\|^2.$$
--
--   **Formalization Note** The spanning hypothesis is placed on the embeddings of modality 2; since $f_1^\star\circ g_1=Qf_2^\star\circ g_2$, it is equivalent to the same hypothesis on modality 1. The paper's gloss after (i), that therefore no statistic of the first two moments of unpaired samples identifies the rotation, is an interpretation of (i) and is not a separate Lean conjunct.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), claim c006; Section 2.2, Proposition 2, PDF p. 4; proof in Appendix A.3, PDF p. 21

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open MeasureTheory Filter Topology Matrix

namespace Arxiv2610_39302

theorem k_pairs_identify_rotation {Z X₁ X₂ : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    (p : Z → ℝ) (π : Z → Z → ℝ) (hπ : IsPairLaw p π) (hk : 1 ≤ k) (hkZ : k < Fintype.card Z)
    (hgap : k + 1 < Fintype.card Z → eigs p π (k + 1) < eigs p π k)
    (g₁ : Z → X₁) (g₂ : Z → X₂) (hg₁ : Function.Injective g₁) (hg₂ : Function.Injective g₂)
    (f₁ : X₁ → Fin k → ℝ) (f₂ : X₂ → Fin k → ℝ)
    (hf₁ : ∀ f : X₁ → Fin k → ℝ, modalityLoss p π sqDist whiteningReg g₁ f₁ ≤ modalityLoss p π sqDist whiteningReg g₁ f)
    (hf₂ : ∀ f : X₂ → Fin k → ℝ, modalityLoss p π sqDist whiteningReg g₂ f₂ ≤ modalityLoss p π sqDist whiteningReg g₂ f) :
    (∀ h : Z → Fin k → ℝ, IsWhitened p h →
      ∀ R : Matrix.orthogonalGroup (Fin k) ℝ, IsWhitened p (fun z => rot R (h z))) ∧
    (∀ Q : Matrix.orthogonalGroup (Fin k) ℝ, (∀ z, f₁ (g₁ z) = rot Q (f₂ (g₂ z))) →
      ∀ (n : ℕ) (zs : Fin n → Z), k ≤ n →
        Submodule.span ℝ (Set.range fun i => f₂ (g₂ (zs i))) = ⊤ →
        (∀ R : Matrix.orthogonalGroup (Fin k) ℝ,
          ∑ i, sqNorm (f₁ (g₁ (zs i)) - rot Q (f₂ (g₂ (zs i)))) ≤
            ∑ i, sqNorm (f₁ (g₁ (zs i)) - rot R (f₂ (g₂ (zs i))))) ∧
        ∀ R : Matrix.orthogonalGroup (Fin k) ℝ,
          (∀ R' : Matrix.orthogonalGroup (Fin k) ℝ,
            ∑ i, sqNorm (f₁ (g₁ (zs i)) - rot R (f₂ (g₂ (zs i)))) ≤
              ∑ i, sqNorm (f₁ (g₁ (zs i)) - rot R' (f₂ (g₂ (zs i))))) → R = Q) := by sorry

end Arxiv2610_39302
