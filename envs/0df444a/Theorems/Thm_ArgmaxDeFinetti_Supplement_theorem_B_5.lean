-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_Supplement_theorem_B_5
-- name    : ArgmaxDeFinetti.Supplement.theorem_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:48:11.669765+00:00
-- url     : https://prove2.me/theorems/0e3914c5-a015-4eeb-8d01-6d6e58a25eb8
-- title:
--   Theorem B.5, pp.65–66 — the rectangular Werner examples are at trace distance $\Omega(\min\{1,t/a\})$ from $\mathrm{SEP}^{(t)}_H(r^2)$ and $\mathrm{SEP}^{(t)}_P(r)$ when $r\ge Ct^2$
-- statement:
--   There are universal constants $C>0$ and $c>0$ such that for all $a,r\in\mathbb N$ and $2\le t\le ar$ with $r\ge Ct^2$:
--
--   1. the $t$-site marginal $\gamma^{(t)}_{a,r}$ of the canonical symmetric purification $\psi_{a,r}$ of the rectangular Werner state satisfies $D_{\mathrm{tr}}(\gamma^{(t)}_{a,r},\sigma)\ge c\min\{1,t/a\}$ for every $\sigma\in\mathrm{SEP}^{(t)}_H(r^2)$ (Hartree mixtures over the composite site $\mathbb C^r\otimes\mathbb C^r$);
--   2. the $t$-site marginal $\omega^{(t)}_{ar,(a^r)}$ of the rectangular Werner state satisfies $D_{\mathrm{tr}}(\omega^{(t)}_{ar,(a^r)},\sigma)\ge c\min\{1,t/a\}$ for every $\sigma\in\mathrm{SEP}^{(t)}_P(r)$.
--
--   In the paper's notation, $D_{\mathrm{tr}}(\gamma^{(t)}_{a,r},\mathrm{SEP}^{(t)}_H(r^2))=\Omega(\min\{1,t/a\})$ and $D_{\mathrm{tr}}(\omega^{(t)}_{ar,(a^r)},\mathrm{SEP}^{(t)}_P(r))=\Omega(\min\{1,t/a\})$. With $N=ar$ and $d=r^2$, resp. $d=r$, the ratio $t/a$ is $t\sqrt d/N$, resp. $td/N$, so together with Theorem 1.3 these match the $t$-site upper bounds up to universal constants: the linear dependence on $t$ cannot be improved.
--
--   **Formalization Note** $\omega$ and $\psi_{a,r}$ are the explicit constructions of the mission's Werner definition, and the marginals are on the first $t$ sites.
--
--   Differences from the source:
--   - reading: "There is a universal constant C > 0" and Ω(min{1, t/a}) → ∃ C > 0 and c > 0, both chosen before a, r, t, with D_tr ≥ c·min{1, t/a}; reason: Ω with universal constants (standing assumption)
--   - encoding: D_tr(γ, SEP) ≥ b (an infimum, (2.5)) → D_tr(γ, σ) ≥ b for every σ in the set; reason: an infimum is ≥ b iff every element is
--   - encoding: ω_{ar,(a^r)}: normalized projector onto the (a^r) Schur–Weyl block; ψ_{a,r}: its canonical symmetric purification → P_W/dim W with W = {v : U^{⊗ar}v = det(U)^a v ∀ unitary U}; ψ = (I ⊗ √ω)|Ω⟩ regrouped into composite sites (E_i, A_i), with √ω = P_W/√dim W; reason: by Schur–Weyl duality the (a^r)-isotypic component is exactly W (S_{(a^r)}(ℂ^r) = det^a); √ of a scaled projector
--   - encoding: SEP^(t)_H(r²) → Hartree mixtures over the site ℂ^r ⊗ ℂ^r indexed by Fin r × Fin r; reason: relabelling of a basis of ℂ^{r²}; same set up to that identification
--   - encoding: the second expressions Ω(min{1, t√d/N}), Ω(min{1, td/N}) → not stated separately; reason: the same quantity with N = ar and d = r², resp. d = r
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Theorem B.5, eqs. (B.18)–(B.19), pp.65–66; definitions of ω_{ar,(a^r)}, ψ_{a,r}, γ^(t)_{a,r}, p.61

import Mathlib
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_ArgmaxDeFinetti_Supplement_marginal
import Definitions.Def_ArgmaxDeFinetti_Supplement_sepT
import Definitions.Def_ArgmaxDeFinetti_Supplement_werner

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- **Theorem B.5 (Optimal t-dependence of the rectangular examples)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), pp.65–66, eqs. (B.18)–(B.19).
There is a universal constant `C > 0` such that, for every `a, r ∈ ℕ` and `2 ≤ t ≤ ar` satisfying `r ≥ Ct²`,
`D_tr(γ^{(t)}_{a,r}, SEP^{(t)}_H(r²)) = Ω(min{1, t/a})` and `D_tr(ω^{(t)}_{ar,(a^r)}, SEP^{(t)}_P(r)) = Ω(min{1, t/a})`.

Stated as: there are universal constants `C, c > 0` such that for all `a, r, t` with `2 ≤ t ≤ ar` and `r ≥ Ct²`,
every `σ ∈ SEP^{(t)}_H(r²)` has `D_tr(γ^{(t)}_{a,r}, σ) ≥ c·min{1, t/a}`, and every `σ ∈ SEP^{(t)}_P(r)` has
`D_tr(ω^{(t)}_{ar,(a^r)}, σ) ≥ c·min{1, t/a}`.

**Formalization Note**
* `ω_{ar,(a^r)}` is `wernerState a r (a*r)` (normalized projector onto the `(a^r)` block, `r` rows of length `a`) and
  `ψ_{a,r}` is `wernerPurif a r (a*r)` (its canonical purification on `ar` composite sites `ℂ^r ⊗ ℂ^r`);
  `γ^{(t)}_{a,r}` and `ω^{(t)}` are their marginals on the first `t` sites.
* `SEP^{(t)}_H(r²)` is the Hartree set over the composite site `ℂ^r ⊗ ℂ^r` (index `Fin r × Fin r`, dimension `r²`).
* `Ω(·)` is "`≥ c ·`" with `c > 0` universal; `C` and `c` are chosen before `a, r, t`. `D_tr(γ, K) ≥ b` (an infimum) is
  "`D_tr(γ, σ) ≥ b` for every `σ ∈ K`". The paper's second expressions `Ω(min{1, t√d/N})`, `Ω(min{1, td/N})` are the
  same quantity with `N = ar` and `d = r²`, resp. `d = r`. -/
theorem theorem_B_5 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a r t : ℕ, 2 ≤ t → t ≤ a * r → C * (t : ℝ) ^ 2 ≤ r →
      (∀ σ ∈ hartreeT (Fin r × Fin r) t,
        c * min 1 ((t : ℝ) / a) ≤
          DimFreeShadow.traceDistance
            (marginal t (Matrix.vecMulVec (wernerPurif a r (a * r)) (star (wernerPurif a r (a * r))))) σ) ∧
      (∀ σ ∈ tensorPowMix (Fin r) t,
        c * min 1 ((t : ℝ) / a) ≤ DimFreeShadow.traceDistance (marginal t (wernerState a r (a * r))) σ) := by sorry

end Supplement

end ArgmaxDeFinetti
