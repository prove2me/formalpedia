-- Prove2me | Theorems.Thm_ConeL2G_claim_4_4
-- name    : ConeL2G.claim_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:42:01.014953+00:00
-- url     : https://prove2.me/theorems/60a3bb5d-0f5d-4411-a331-bf749675d574
-- title:
--   Claim 4.4 — $\|P_if_i\|_\mu\le\|D_if_i\|_\mu/\sqrt{(\ell_1-1)(\ell_2-1)-1}$
-- statement:
--   Let $H$ be a single edge between vertices $1$ and $2$ with color lists $L_1,L_2$ of sizes $\ell_1,\ell_2\ge s+1$, where $s\ge5$ is real, and let $\mu$ be uniform on its proper list colorings. For $i\in\{1,2\}$ let $f_i:L_i\to\mathbb R$ satisfy $\sum_{c\in L_i}f_i(c)=0$, viewed as the function $(x_1,x_2)\mapsto f_i(x_i)$. Then for $i\in\{1,2\}$
--   $$\|P_if_i\|_\mu\ \le\ \frac{\|D_if_i\|_\mu}{\sqrt{(\ell_1-1)(\ell_2-1)-1}} .$$
--
--   These are the hypotheses under which the claim is stated in the proof of Lemma 4.3 (the decomposition (10) of the degree-one part); the claim bounds the averaging operator on centered single-coordinate functions.
--
--   Differences from the source:
--   - encoding: f_i : L_i → ℝ with Σ_{c∈L_i} f_i(c) = 0, extended to Ω as a function of x_i → g : Fin K → ℝ with Σ_{c ∈ L i} g c = 0, lifted to x ↦ g (x i); reason: on Ω, x_i ∈ L_i, so the values of g outside L_i never enter; same instances
--   - encoding: vertices 1 and 2 → vertices 0 and 1 of Fin 2; no edge is ⊥, one edge is ⊤; reason: relabelling; same instances
--   - encoding: a subgraph H of G with the lists left after pinning G ∖ H (Section 2.1) → an arbitrary finite graph with arbitrary lists; reason: every finite graph with lists is such a pinned subgraph (take G = H), and every pinned subgraph is a finite graph with lists; same instances
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Claim 4.4, p.15 (setting: proof of Lemma 4.3, pp.11–12, Eq. (10))

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_ConeL2G_unifMass

namespace ConeL2G

/-- **Claim 4.4 (the averaging operator on a single-coordinate centered function).**
Li–Oveis Gharan, arXiv:2610.37721, Claim 4.4, p.15: "For `i ∈ {1, 2}`, we have
`‖Pᵢfᵢ‖_µ ⩽ ‖Dᵢfᵢ‖_µ / √((ℓ₁ − 1)(ℓ₂ − 1) − 1)`."

Its hypotheses are the setting of the proof of Lemma 4.3 (pp.11–12), where it is stated: one edge
between vertices 1 and 2, `s ⩾ 5`, lists of sizes `ℓ₁, ℓ₂ ⩾ s + 1`, and `fᵢ : Lᵢ → ℝ` with
`Σ_{c∈Lᵢ} fᵢ(c) = 0` (Eq. (10)), viewed on `Ω` as the function `(x₁, x₂) ↦ fᵢ(xᵢ)`.

**Formalization Note.** Vertices 1, 2 are `0, 1 : Fin 2`, the graph is `⊤`; `fᵢ` is `g : Fin K → ℝ`
with `Σ_{c ∈ L i} g c = 0`, lifted to `x ↦ g (x i)`. `Pᵢ = SpinGirth5.heatBath µ i`,
`Dᵢ = SpinGirth5.singleLap µ i`, `‖g‖_µ = √⟨g, g⟩_µ`. -/
theorem claim_4_4 {K : ℕ} (L : Fin 2 → Finset (Fin K)) (s : ℝ) (hs : 5 ≤ s)
    (hL0 : s + 1 ≤ ((L 0).card : ℝ)) (hL1 : s + 1 ≤ ((L 1).card : ℝ)) :
    ∀ (i : Fin 2) (g : Fin K → ℝ), ∑ c ∈ L i, g c = 0 →
      Real.sqrt (MarkovMixing.innerPi (unifMass ⊤ L)
          (SpinGirth5.heatBath (unifMass ⊤ L) i (fun x => g (x i)))
          (SpinGirth5.heatBath (unifMass ⊤ L) i (fun x => g (x i)))) ≤
        Real.sqrt (MarkovMixing.innerPi (unifMass ⊤ L)
            (SpinGirth5.singleLap (unifMass ⊤ L) i (fun x => g (x i)))
            (SpinGirth5.singleLap (unifMass ⊤ L) i (fun x => g (x i)))) /
          Real.sqrt ((((L 0).card : ℝ) - 1) * (((L 1).card : ℝ) - 1) - 1) := by sorry

end ConeL2G
