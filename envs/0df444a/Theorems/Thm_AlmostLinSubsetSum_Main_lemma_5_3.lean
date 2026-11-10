-- Prove2me | Theorems.Thm_AlmostLinSubsetSum_Main_lemma_5_3
-- name    : AlmostLinSubsetSum.Main.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:29:46.200493+00:00
-- url     : https://prove2.me/theorems/2ce683f6-f659-4517-b113-a9404ced825d
-- title:
--   Lemma 5.3 — boundary shell: $\mathrm{vol}\bigl(\bigcup_p(p+M_p)\bigr)\le 50d\,3^{d-1}\eta\,\mathrm{vol}(\tau\cdot Q)$
-- statement:
--   **Lemma 5.3** (Boundary shell, p. 21). The union of the regions $p+M_p$ over all boundary centers $p$ has volume at most $50d\,3^{d-1}\eta\,\mathrm{vol}(\tau\cdot Q)$.
--
--   Setting: $d\ge1$; $Z=Z(V)=\sum_{i\in I}[0,v_i]$ for a finite family $v_i\in\mathbb Z^d$; a box $Q=\prod_j[-q_j,q_j]$ with $q_j\ge1$; an integer $\tau\ge1$; $o\in\mathbb Z^d$; $0<\eta\le1/10$; $K:=(Z+10\eta\tau\cdot Q)\cap(o+3\tau\cdot Q)$ and $M_p:=(K-p)\cap(p-K)$. For every set $B$ of boundary centers ($p\in Z\cap(o+2\tau\cdot Q)$ with $p+10\eta\tau\cdot Q\not\subseteq Z$),
--   $$\mathrm{vol}\Bigl(\bigcup_{p\in B}(p+M_p)\Bigr)\le 50d\,3^{d-1}\eta\cdot\mathrm{vol}(\tau\cdot Q),$$
--   with Lebesgue measure on $\mathbb R^d$.
--
--   Differences from the source:
--   - generalization: boundary centers are rational points (Definition 4.4) → any real point p satisfying (11); reason: the proof never uses rationality; rational centers are a special case
--   - generalization: the boundary centers of the prepared instance (Lemma 4.5), Z = Z(V) of its spanning items, and the fixed sufficiently small constant η of (3) → any set of boundary centers, Z of any finite integer family, any η ∈ (0, 1/10]; reason: the proof uses only (11), Q = −Q, q_j > 0 and η ≤ 1/10 (Lemma 5.2); the paper's data are one instance
--   - encoding: volume → MeasureTheory.volume on Fin d → ℝ, in ℝ≥0∞, with the constant as ENNReal.ofReal; reason: Lebesgue measure; the union need not be shown measurable for an outer-measure bound
-- source:
--   Chen, Mao, Zhang (2026), An Almost-Linear Time Algorithm for Multidimensional Subset Sum, STOC 2027 submission, SHA-256 0cd42ca048cfff088013ad06450a278a6df72a29004c48c5c138f3f6df85d1e0, Lemma 5.3, p. 21

import Mathlib
import Definitions.Def_AlmostLinSubsetSum_Main_Basic
import Definitions.Def_AlmostLinSubsetSum_Main_Geometry

set_option autoImplicit false

namespace AlmostLinSubsetSum.Main

/-- **Lemma 5.3** (Boundary shell; Chen, Mao, Zhang 2026, p. 21). The union of the regions
`p + M_p` over all boundary centers `p` has volume at most `50 d 3^{d−1} η vol(τ · Q)`.

Setting (§4.4–5.1): `Z = Z(V)` for a finite family `V ⊆ ℤ^d`; a box `Q = ∏_j [−q_j, q_j]`
with `q_j ≥ 1`; an integer scale `τ ≥ 1`; `o ∈ ℤ^d`; `0 < η ≤ 1/10`;
`K := (Z + 10ητ · Q) ∩ (o + 3τ · Q)` and `M_p := (K − p) ∩ (p − K)`. The union is over an
arbitrary set `B` of boundary centers (points `p ∈ Z ∩ (o + 2τ · Q)` with `p + 10ητ · Q ⊄ Z`).
Volume is Lebesgue measure on `ℝ^d`. -/
theorem lemma_5_3 {ι : Type*} {d : ℕ} (hd : 1 ≤ d) (I : Finset ι) (v : ι → Fin d → ℤ)
    (q : Fin d → ℝ) (hq : ∀ j, 1 ≤ q j) (τ : ℕ) (hτ : 1 ≤ τ) (o : Fin d → ℤ)
    (η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 10)
    (B : Set (Fin d → ℝ))
    (hB : ∀ p ∈ B, IsBoundaryCenter (zonotope I (fun i => toReal (v i))) q o η τ p) :
    MeasureTheory.volume (⋃ p ∈ B,
        translate p (macbeathM (shellBody (zonotope I (fun i => toReal (v i))) q o η τ) p)) ≤
      ENNReal.ofReal (50 * d * 3 ^ (d - 1) * η) *
        MeasureTheory.volume (dilate (τ : ℝ) (box q)) := by sorry

end AlmostLinSubsetSum.Main
