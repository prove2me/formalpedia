-- Prove2me | Theorems.Thm_AvgPHETH_lemma_6_1
-- name    : AvgPHETH.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:44.133312+00:00
-- url     : https://prove2.me/theorems/be684c6d-00aa-415f-9b1a-7cf2c8208ae6
-- title:
--   Lemma 6.1 — Inductive Compression: one $\mathrm S_2$ operator saves a logarithmic factor
-- statement:
--   Fix constants $k\ge0$, $d\ge1$, $0<\alpha<\beta<1$ and quantifiers $Q_1,\dots,Q_d\in\{\exists,\forall\}$. Let $\ell\in\mathcal L_{\downarrow k}$ and consider
--
--   $$G_n(z)=Q_1y_1\cdots Q_dy_d\,V_n(z,y_1,\dots,y_d),\qquad|y_i|=\ell(n),\ |z|\le\mathrm{poly}(n),$$
--
--   where $V_n$ is computable with oracle $O$ in time $2^{O(n^\alpha)}$ uniformly in $n$ and all its inputs. Assume $\Sigma_d^{p,O}\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$. Then there are a polynomial $p$, a length function $\ell'\in\mathcal L_{\downarrow(k+1)}$ and a predicate $V'_n$ uniformly computable with oracle $O$ in time $2^{O(n^\beta)}$ such that
--
--   $$G'_n(z,z_E,z_U)=Q_2y'_2\cdots Q_dy'_d\,V'_n(z,z_E,z_U,y'_2,\dots,y'_d),\qquad|y'_i|=\ell'(n),$$
--
--   satisfies for every sufficiently large $n$ and every $z\in\{0,1\}^{\le\mathrm{poly}(n)}$ the $\mathrm S_2$ condition
--
--   $$G_n(z)=1\implies\exists z_E\,\forall z_U\;G'_n(z,z_E,z_U)=1,\qquad G_n(z)=0\implies\exists z_U\,\forall z_E\;G'_n(z,z_E,z_U)=0,$$
--
--   with $z_E,z_U\in\{0,1\}^{p(n)}$. Each application removes one quantifier and saves one logarithmic factor in the move length.
--
--   Differences from the source:
--   - generalization: the unrelativized statement under $\mathrm{Dist}\Sigma_d^p\subseteq\mathrm{AvgP}$ → relative to every oracle $O$, under $\Sigma_d^{p,O}\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$; reason: Remark 6.4 (p.28), p.29 and p.30 use this form; at $O=\emptyset$ the footnote on p.10 gives the hypothesis from the printed one
--   - encoding: $V_n$ and $V'_n$ uniformly computable → one machine each, on input $(1^n,z,\dots)$, within $\lceil2^{Cn^\alpha}\rceil+C$ steps; reason: this is the meaning of uniformity; the summand only matters for small $n$
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Lemma 6.1, p.24 (PDF 26)

import Mathlib
import Definitions.Def_AvgPHETH_TimesUT
import Definitions.Def_AvgPHETH_SigmaPO
import Definitions.Def_AvgPHETH_LDown
import Definitions.Def_AvgPHETH_Game
import Definitions.Def_AvgPHETH_expTime
import Definitions.Def_AvgPHETH_acceptsAt
import Definitions.Def_AvgPHETH_unary
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_tupleEnc
open KarpLiptonOM

namespace AvgPHETH

/-- **Lemma 6.1 (Inductive Compression)** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.24 (PDF 26)), relative to every oracle `O` (Remark 6.4, p.28 (PDF 30); p.29 (PDF 31)). Fix `k ≥ 0`, `d ≥ 1`,
`0 < α < β < 1` and quantifiers `Q₁, …, Q_d`. Let `ℓ ∈ 𝓛_{↓k}` and `G_n(z) = Q₁y₁ ⋯ Q_d y_d V_n(z, y₁, …, y_d)`, `|y_i| = ℓ(n)`, `|z| ≤ poly(n)`, where `V_n` is
computable in time `2^{O(n^α)}` uniformly in `n` and all its inputs. Assume `Σ_d^{p,O} × {U, T} ⊆ AvgP^O`. Then there are a polynomial `p`, `ℓ' ∈ 𝓛_{↓(k+1)}` and `V'_n`
uniformly computable in time `2^{O(n^β)}` such that `G'_n(z, z_E, z_U) = Q₂y'₂ ⋯ Q_d y'_d V'_n(z, z_E, z_U, y'₂, …, y'_d)`, `|y'_i| = ℓ'(n)`, satisfies the `S₂` condition for every
sufficiently large `n` and every `z`: `G_n(z) = 1 ⟹ ∃z_E ∀z_U G'_n = 1` and `G_n(z) = 0 ⟹ ∃z_U ∀z_E G'_n = 0`, with `z_E, z_U ∈ {0,1}^{p(n)}`.

**Formalization Note** `Qs` is an arbitrary quantifier list (`true` is `∃`), not necessarily alternating; for `d = 1`, `G'` is `V'` itself. `V_n` and `V'_n` are one machine each, on the
input `(1^n, z, …)`. -/
theorem lemma_6_1 (O : Set (List Bool)) (k d : ℕ) (hd : 1 ≤ d) (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hβ : β < 1) (Qs : List Bool) (hQs : Qs.length = d) (ℓ : ℕ → ℕ) (hℓ : ℓ ∈ LDown k id)
    (r : Polynomial ℕ) (M : OracleTM) (C : ℕ)
    (hM : ∀ (n : ℕ) (z : List Bool) (ys : List (List Bool)), z.length ≤ r.eval n →
      ys.length = d → (∀ y ∈ ys, y.length = ℓ n) →
      M.HaltsWithin O (expTime C α n) (tupleEnc ([unary n, z] ++ ys)))
    (hAvg : TimesUT O (SigmaPO O d)) :
    ∃ (p : Polynomial ℕ), ∃ ℓ' ∈ LDown (k + 1) id, ∃ (M' : OracleTM) (C' n₀ : ℕ),
      (∀ (n : ℕ) (z zE zU : List Bool) (ys : List (List Bool)), z.length ≤ r.eval n →
        zE.length = p.eval n → zU.length = p.eval n → ys.length = d - 1 →
        (∀ y ∈ ys, y.length = ℓ' n) →
        M'.HaltsWithin O (expTime C' β n) (tupleEnc ([unary n, z, zE, zU] ++ ys))) ∧
      ∀ n ≥ n₀, ∀ z : List Bool, z.length ≤ r.eval n →
        (Game Qs (ℓ n) (fun ys => acceptsAt M O (expTime C α n) (tupleEnc ([unary n, z] ++ ys))) →
          ∃ zE : List Bool, zE.length = p.eval n ∧ ∀ zU : List Bool, zU.length = p.eval n →
            Game Qs.tail (ℓ' n) (fun ys =>
              acceptsAt M' O (expTime C' β n) (tupleEnc ([unary n, z, zE, zU] ++ ys)))) ∧
        (¬ Game Qs (ℓ n) (fun ys => acceptsAt M O (expTime C α n) (tupleEnc ([unary n, z] ++ ys))) →
          ∃ zU : List Bool, zU.length = p.eval n ∧ ∀ zE : List Bool, zE.length = p.eval n →
            ¬ Game Qs.tail (ℓ' n) (fun ys =>
              acceptsAt M' O (expTime C' β n) (tupleEnc ([unary n, z, zE, zU] ++ ys)))) := by sorry

end AvgPHETH
