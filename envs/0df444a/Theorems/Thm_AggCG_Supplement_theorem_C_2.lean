-- Prove2me | Theorems.Thm_AggCG_Supplement_theorem_C_2
-- name    : AggCG.Supplement.theorem_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:29:32.220291+00:00
-- url     : https://prove2.me/theorems/c2bb5818-609f-410b-aeb0-c406f0c60683
-- title:
--   Theorem C.2 — robust observation compiler
-- statement:
--   Suppose code witnesses $\theta_b$ realize every binary word and the $i$th probe loss decomposes as
--
--   $$
--   f_{\theta_b}(x_i)=a_i+\Delta_i b_i+h_i(b_{-i})+e_i(b),
--   $$
--
--   where $h_i$ is independent of $b_i$, has oscillation at most $\omega_i$, $|e_i(b)|\le\varepsilon_i$, and $\Delta_i>\omega_i+2\varepsilon_i$. Then the probes are $\gamma$-fat-shattered for every $0<\gamma\le\frac12\min_i(\Delta_i-\omega_i-2\varepsilon_i)$, and hence $\operatorname{fat}_\gamma\ge d$.
--
--   Differences from the source:
--   - generalization: the source invokes efficient-code witnesses and legal probes → Lean assumes only the exact code and signal/interference/error hypotheses used in the conclusion; reason: every efficient legal family in the source is an instance, while the omitted computational qualifiers play no role in fat-shattering
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), Theorem C.2, pp.19–20, PDF pp.20–21; Lemma A.4, p.15, PDF p.16

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering

namespace AggCG.Supplement

open BartlettNN.Margin

/-- **Theorem C.2** (Robust observation compiler; Sharma, *Computational Complexity of Data-Driven
Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission
(manuscript sha256 f7ea0248…), pp.19–20, PDF pp.20–21), with the hypotheses of Lemma A.4 (p.15, PDF p.16)
and the code of Definition A.1 (p.14, PDF p.15). Let `{f_θ : θ ∈ Θ}` be a family of losses on instances
`X`, `B : Θ → {0,1}^d` a code with witnesses `θ_b` (`B(θ_b) = b`), and `x_1, …, x_d` instances whose
losses at the witnesses are `f_{θ_b}(x_i) = a_i + Δ_i b_i + h_i(b_{−i}) + e_i(b)`, with `h_i` not depending
on `b_i`, `osc(h_i) ≤ ω_i`, `|e_i(b)| ≤ ε_i` and `Δ_i > ω_i + 2ε_i`. Then for every
`0 < γ ≤ ½ min_i(Δ_i − ω_i − 2ε_i)` the instances are `γ`-fat-shattered (non-strict convention), so
`fat_γ(F) ≥ d`.

**Formalization Note** The computational qualifiers of Definition A.1 ("efficient", polynomial-time
`Encode`, polynomial-bit witnesses, "legal" probes) carry no formal content in the conclusion and are not
assumed; nor is `f_θ ∈ [0, 1]`. Fat-shattering is the published `BartlettNN.Margin.GammaShatters`
(`(g(x_i) − r_i)·(±1) ≥ γ`), and `fat` its `ℕ∞`-valued dimension. -/
theorem theorem_C_2 {Θ X : Type*} (f : Θ → X → ℝ) (d : ℕ) (B : Θ → Fin d → Bool)
    (θw : (Fin d → Bool) → Θ) (hB : ∀ b, B (θw b) = b) (x : Fin d → X)
    (a Δ ω ε : Fin d → ℝ) (hfun e : Fin d → (Fin d → Bool) → ℝ)
    (hdec : ∀ b i, f (θw b) (x i) = a i + Δ i * (if b i then 1 else 0) + hfun i b + e i b)
    (hind : ∀ i b b', (∀ j, j ≠ i → b j = b' j) → hfun i b = hfun i b')
    (hosc : ∀ i b b', hfun i b - hfun i b' ≤ ω i)
    (herr : ∀ i b, |e i b| ≤ ε i)
    (hgap : ∀ i, ω i + 2 * ε i < Δ i)
    (γ : ℝ) (hγ : 0 < γ) (hγle : ∀ i, γ ≤ (Δ i - ω i - 2 * ε i) / 2) :
    GammaShatters {g : X → ℝ | ∃ θ, g = f θ} γ x ∧
      (d : ℕ∞) ≤ fat {g : X → ℝ | ∃ θ, g = f θ} γ := by sorry

end AggCG.Supplement
