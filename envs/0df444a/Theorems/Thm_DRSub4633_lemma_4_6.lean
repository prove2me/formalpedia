-- Prove2me | Theorems.Thm_DRSub4633_lemma_4_6
-- name    : DRSub4633.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:09:47.495646+00:00
-- url     : https://prove2.me/theorems/0e2297c6-da84-4a5c-8f57-4e87546af2f9
-- title:
--   Lemma 4.6 — path comparisons with remainders
-- statement:
--   Let $f$ be nonnegative, continuously differentiable and DR-submodular on $Q$ and fix $x\in Q$. For every comparator $o=(o_S,o_L)\in Q$ and every $t\in[0,1]$, with $\tilde o_S=a(t)+(1-a(t))o_S$, $E^*=e(o_S)$ and the objects $\Delta_l$, $\Delta_o$, $\Delta_0$, $X_i^\pm$, $\Xi_o$, $L_o$, $T_P$ of p.18,
--   $$F(o)+S_1(t)=C(t)+\langle g^L(t),o_L-v\rangle+\langle(1-a(t))V(t),o_S\rangle+(c_1-1)E(t)+E^*-c_1Q_t(o_S),\tag{38}$$
--   $$F(o)+S_2(t)=C(t)+\langle g^L(t),o_L-v\rangle+\langle(1-a(t))\nabla_SF(a(t),0_L),o_S\rangle+E^*-Q_t(o_S),\tag{39}$$
--   $$F(o_S,0_L)+S_3(t)=S_0(t)+\langle(1-a(t))\nabla_SF(a(t),0_L),o_S\rangle+E^*-Q_t(o_S),\tag{40}$$
--   $$F(0_S,o_L)+S_4(t)=C(t)-E(t)+\langle g^L(t),o_L-v\rangle,\tag{41}$$
--   $$F(o)+S_5=F(o_S,0_L)+F(0_S,o_L),\tag{42}$$
--   with the nonnegative remainders
--   $$S_1(t)=L_o(\tilde o_S)+\Xi_o(\tilde o_S)-\Xi_o(a(t))+\Delta_o(\tilde o_S)-\Delta_o(o_S)+\sum_{i=1}^m\chi_iT_{P_i^+}(t),$$
--   $$S_2(t)=L_o(a(t))+\Delta_o(\tilde o_S)-\Delta_o(o_S)+(\Delta_0-\Delta_o)(\tilde o_S)-(\Delta_0-\Delta_o)(a(t))+T_{0_L}(t),$$
--   $$S_3(t)=\Delta_0(\tilde o_S)-\Delta_0(o_S)+T_{0_L}(t),\quad S_4(t)=\Delta_o(a(t))+L_o(a(t)),\quad S_5=(\Delta_0-\Delta_o)(o_S).$$
--   Here $\Delta_l(y)=F(y,l)-F(0_S,l)-e(y)$, $X_i^+=\Delta_{P_i^+}-\Delta_{P_{i-1}^+}$, $X_i^-=\Delta_{P_{i-1}^-}-\Delta_{P_i^-}$, $\Xi_o=\sum_i\frac{q_i-v_i(1-o_i)}{b}X_i^++\sum_i\frac{b}{v_i}o_iX_i^-$, $L_o(y)$ is the gap in (30) for $J=F(y,\cdot)$ at $o_L$, and $T_P(t)=F(a(t),P)+\langle(1-a(t))\nabla_SF(a(t),P),o_S\rangle-F(\tilde o_S,P)$.
--
--   The identities and the signs of the remainders together are what the proof of Theorem 4.1 averages in time.
--
--   Differences from the source:
--   - encoding: objective defined on Q only; R^n with coordinatewise order; C^1 with boundary derivatives the continuous extensions of interior ones → f a total function on EuclideanSpace ℝ (Fin n), hypotheses on the cube only, values off the cube never read; the order written coordinatewise; GeomDRSub.IsDRSubmodular (ContDiffOn ℝ 1 on the cube, fderivWithin the cube); reason: Lean convention; on the cube the within-cube derivative of a C^1 function is the continuous extension of the interior derivative, so the instances are the same
--   - encoding: L includes a dummy coordinate of state 1, label 1, weight q = 1, zero field component → only the original coordinates are represented; the dummy enters as label 1 with q_1 = 1 and its zero terms are dropped; reason: F does not depend on the dummy coordinate (p.10), so every dropped term is zero; same instances
--   - encoding: block vectors o_S, o_L, r, l indexed by S and L → functions on Fin n of which only the relevant block is read (mergePt); reason: Lean convention; same instances
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma 4.6, pp.18–19

import Mathlib
import Definitions.Def_GeomDRSub_IsDRSubmodular
import Definitions.Def_DRSub4633_Cconst
import Definitions.Def_DRSub4633_gLarge
import Definitions.Def_DRSub4633_Vgrad
import Definitions.Def_DRSub4633_QFace
import Definitions.Def_DRSub4633_c1
import Definitions.Def_DRSub4633_Pminus
import Definitions.Def_DRSub4633_qLarge

namespace DRSub4633

/-- **Lemma 4.6 (Path comparisons with remainders).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma 4.6, pp.18–19: "For every
comparator `o = (o_S, o_L)` and every `t ∈ [0, 1]`, (38)–(42) [hold], with the nonnegative
remainders `S₁(t), …, S₄(t), S₅`."

Standing hypotheses (Sections 3.1 and 4.1, pp.7–10): `f` nonnegative, `C¹` and DR-submodular on
`Q = [0, 1]^n`; `x ∈ Q` is the fixed state.

The objects are those of p.18: `õ_S = a(t) + (1 − a(t))o_S`, `E* = e(o_S)`;
`Δ_l(y) = F(y, l) − F(0_S, l) − e(y)`, `Δ_o = Δ_(o_L)`, `Δ₀ = Δ_(0_L)`;
`X⁺ᵢ(y) = Δ_(P⁺ᵢ)(y) − Δ_(P⁺ᵢ₋₁)(y)`, `X⁻ᵢ(y) = Δ_(P⁻ᵢ₋₁)(y) − Δ_(P⁻ᵢ)(y)`;
`Ξ_o(y) = ∑ᵢ [qᵢ − vᵢ(1 − oᵢ)]/b · X⁺ᵢ(y) + ∑ᵢ (b/vᵢ) oᵢ X⁻ᵢ(y)`;
`L_o(y)` the gap in (30) for `J = F(y, ·)` at `o_L` (right side of (30) minus `J(o_L)`);
`T_P(t) = F(a(t), P) + ⟨(1 − a(t))∇_S F(a(t), P), o_S⟩ − F(õ_S, P)`; and
`S₁(t) = L_o(õ_S) + Ξ_o(õ_S) − Ξ_o(a(t)) + Δ_o(õ_S) − Δ_o(o_S) + ∑ᵢ χᵢ T_(P⁺ᵢ)(t)`,
`S₂(t) = L_o(a(t)) + Δ_o(õ_S) − Δ_o(o_S) + (Δ₀ − Δ_o)(õ_S) − (Δ₀ − Δ_o)(a(t)) + T_(0_L)(t)`,
`S₃(t) = Δ₀(õ_S) − Δ₀(o_S) + T_(0_L)(t)`, `S₄(t) = Δ_o(a(t)) + L_o(a(t))`, `S₅ = (Δ₀ − Δ_o)(o_S)`.

**Formalization Note.** Block vectors are functions on `Fin n` (`mergePt` reads the small block on
`S` and the large block on `L`); `o ∈ Q` supplies both blocks. The dummy large coordinate (label
`1`) contributes zero to every sum (its prefix vectors coincide on the original coordinates and its
field component vanishes), so the sums over large labels run over the original large coordinates
`j` with label `largePos x j`; the comparator's dummy value is immaterial. `∇_S F` is
`GeomDRSub.pd` of `F`. -/
theorem lemma_4_6 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf0 : ∀ y ∈ GeomDRSub.cube n, 0 ≤ f y) (hf : GeomDRSub.IsDRSubmodular f)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ GeomDRSub.cube n)
    (o : EuclideanSpace ℝ (Fin n)) (ho : o ∈ GeomDRSub.cube n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let Lg : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => sPar < x j)
    let Sm : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => x j ≤ sPar)
    let a : Fin n → ℝ := aPath x t
    let ot : Fin n → ℝ := fun j => a j + (1 - a j) * o j
    let Fv : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun y l => resid f x (mergePt x y l)
    let e : (Fin n → ℝ) → ℝ := eFace f x
    let Δ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun l y => Fv y l - Fv 0 l - e y
    let Δo : (Fin n → ℝ) → ℝ := Δ (fun j => o j)
    let Δ0 : (Fin n → ℝ) → ℝ := Δ 0
    let Estar : ℝ := e (fun j => o j)
    let Qo : ℝ := QFace f x t (fun j => o j)
    let E : ℝ := Ypath f x 0 t
    let m : ℕ := mLarge x
    let Xp : Fin n → (Fin n → ℝ) → ℝ := fun j y =>
      Δ (Pplus x (largePos x j)) y - Δ (Pplus x (largePos x j - 1)) y
    let Xm : Fin n → (Fin n → ℝ) → ℝ := fun j y =>
      Δ (Pminus x (largePos x j - 1)) y - Δ (Pminus x (largePos x j)) y
    let Ξo : (Fin n → ℝ) → ℝ := fun y =>
      ∑ j ∈ Lg, (qLarge x j - x j * (1 - o j)) / bPar * Xp j y +
        ∑ j ∈ Lg, bPar / x j * o j * Xm j y
    let Lo : (Fin n → ℝ) → ℝ := fun y =>
      let Aj : Fin n → ℝ := fun j =>
        (Fv y (Pminus x (largePos x j)) - Fv y (Pminus x (largePos x j - 1))) / pLarge x j
      let Bj : Fin n → ℝ := fun j =>
        (Fv y (Pplus x (largePos x j - 1)) - Fv y (Pplus x (largePos x j))) / (1 - pLarge x j)
      (Fv y (Pplus x m) - ∑ j ∈ Lg, pLarge x j * Bj j
        + ∑ j ∈ Lg, ((1 - pLarge x j) * Aj j + pLarge x j * Bj j) * o j) - Fv y (fun j => o j)
    let TP : (Fin n → ℝ) → ℝ := fun P =>
      Fv a P + ∑ j ∈ Sm, (1 - a j) * GeomDRSub.pd (resid f x) j (mergePt x a P) * o j - Fv ot P
    let gLo : ℝ := ∑ j ∈ Lg, gLarge f x t j * (o j - x j)
    let S1 : ℝ := Lo ot + Ξo ot - Ξo a + Δo ot - Δo (fun j => o j) +
      ∑ i ∈ Finset.Icc 1 m, chi x i * TP (Pplus x i)
    let S2 : ℝ := Lo a + Δo ot - Δo (fun j => o j) + (Δ0 ot - Δo ot) - (Δ0 a - Δo a) + TP 0
    let S3 : ℝ := Δ0 ot - Δ0 (fun j => o j) + TP 0
    let S4 : ℝ := Δo a + Lo a
    let S5 : ℝ := Δ0 (fun j => o j) - Δo (fun j => o j)
    -- (38)
    resid f x o + S1 = Cconst f x t + gLo + ∑ j ∈ Sm, (1 - a j) * Vgrad f x t j * o j
        + (c1 - 1) * E + Estar - c1 * Qo ∧
    -- (39)
    resid f x o + S2 = Cconst f x t + gLo
        + ∑ j ∈ Sm, (1 - a j) * GeomDRSub.pd (resid f x) j (mergePt x a 0) * o j + Estar - Qo ∧
    -- (40)
    Fv (fun j => o j) 0 + S3 = S0path f x t
        + ∑ j ∈ Sm, (1 - a j) * GeomDRSub.pd (resid f x) j (mergePt x a 0) * o j + Estar - Qo ∧
    -- (41)
    Fv 0 (fun j => o j) + S4 = Cconst f x t - E + gLo ∧
    -- (42)
    resid f x o + S5 = Fv (fun j => o j) 0 + Fv 0 (fun j => o j) ∧
    -- the remainders are nonnegative
    0 ≤ S1 ∧ 0 ≤ S2 ∧ 0 ≤ S3 ∧ 0 ≤ S4 ∧ 0 ≤ S5 := by sorry

end DRSub4633
