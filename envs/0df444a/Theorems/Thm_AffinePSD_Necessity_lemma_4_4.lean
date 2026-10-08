-- Prove2me | Theorems.Thm_AffinePSD_Necessity_lemma_4_4
-- name    : AffinePSD.Necessity.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:28.830028+00:00
-- url     : https://prove2.me/theorems/8520ec72-80fb-4b3c-b72d-c233c4b19ec0
-- title:
--   Lemma 4.4 — additive (resp. homogeneous additive) maps on $S_d^+$ extend to additive (resp. linear) maps
-- statement:
--   Let $V$ be a real vector space and $L : S_d^+ \to V$.
--
--   1. If $L$ is additive, i.e. $L(x + y) = L(x) + L(y)$ for all $x, y \in S_d^+$, then $L$ is the restriction of an additive map on $S_d$.
--   2. If $L$ is homogeneous additive, i.e.
--   $$L(x + \lambda y) = L(x) + \lambda L(y) \qquad \text{for all } x, y \in S_d^+,\ \lambda \in \mathbb R_+,$$
--   then $L$ is the restriction of an $\mathbb R$-linear map on $S_d$.
--
--   In the proof of Proposition 4.9 this is applied with $V = S_d$, the space of linear maps on $S_d$, and the space of finite signed measures, to show that the diffusion, drift and jump characteristics depend linearly on the state.
--
--   **Formalization Note.** The extension is stated on $M_d \supseteq S_d$. A map on $M_d$ restricts to $S_d$, and a map on $S_d$ composed with $x \mapsto (x+x^\top)/2$ extends to $M_d$ with the same additivity or linearity, so the two readings are equivalent. The hypotheses are stated for every proof that $x + \lambda y$ lies in the cone.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Lemma 4.4 and footnote 8, p. 20

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Cone

namespace AffinePSD.Necessity

/-- Lemma 4.4 (arXiv:0910.0137v3, §4, p. 20). Let `V` be a vector space over `ℝ` and `L : S_d^+ → V` an
additive (resp. homogeneous additive) map, i.e. `L(x + λy) = L(x) + λL(y)` for all `x, y ∈ S_d^+` and
`λ = 1` (resp. all `λ ∈ ℝ_+`). Then `L` is the restriction of an additive (resp. `ℝ`-linear) map on `S_d`.

**Formalization Note.** The extension is stated on `M_d ⊇ S_d`: a map on `M_d` restricts to `S_d`, and a
map on `S_d` composed with `x ↦ (x + x^⊤)/2` extends to `M_d` with the same additivity/linearity, so the
two readings are equivalent. The hypotheses quantify over a proof that `x + λy ∈ S_d^+`. -/
theorem lemma_4_4 {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V] (L : Cone d → V) :
    ((∀ (x y : Cone d) (h : PSD ((x : Mat d) + (y : Mat d))), L ⟨_, h⟩ = L x + L y) →
      ∃ L' : Mat d →+ V, ∀ x : Cone d, L' x = L x) ∧
    ((∀ (x y : Cone d) (c : ℝ), 0 ≤ c → ∀ h : PSD ((x : Mat d) + c • (y : Mat d)),
        L ⟨_, h⟩ = L x + c • L y) →
      ∃ L' : Mat d →ₗ[ℝ] V, ∀ x : Cone d, L' x = L x) := by sorry

end AffinePSD.Necessity
