-- Prove2me | Theorems.Thm_CopylessCRA_lemma_15
-- name    : CopylessCRA.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:00.961864+00:00
-- url     : https://prove2.me/theorems/5ae29bbf-dc80-4a78-96b7-11d4007aa024
-- title:
--   Lemma 15 (Local quotients), p.10 — $W/N\cong\mathbb Q^d/K_u$, intertwining $B_z$ with $M_z$
-- statement:
--   Let a CCRA compute $f$, let $(\lambda,M,\gamma)$ be a minimal representation of $f$ with invertible letter matrices, $t$ a word with $|\delta(S,t)|$ minimal, $S_{ret}=\delta(S,t)$, $e=t^{|S_{ret}|!}$. Let $u\in\Sigma^*$, $q=\delta(s_0,ue)$ and $x_u=P_{s_0,ue}(x^{(0)})$. Let $L_{S_{ret}}$ act on $\mathbb Q^r$ by $P_z=P_{q,z}$, and for $s\in\Sigma^*$ let $o_s=\omega_{\delta(q,s)}\circ P_{q,s}\in V_r$. Put
--   $$W=\operatorname{span}\{o_s\},\quad N=\{h\in W:(B_zh)(x_u)=0\ \forall z\in L_{S_{ret}}\},\quad K_u=\{v\in\mathbb Q^d:\lambda M_{ue}M_zv=0\ \forall z\in L_{S_{ret}}\}.$$
--   Then
--
--   1. $q\in S_{ret}$;
--   2. $W$ and $N$ are invariant under every $B_z$ ($z\in L_{S_{ret}}$), and $K_u$ under every $M_z$;
--   3. $K_u$ is $\mathcal K$-invariant: every $g\in\mathcal K$ maps $K_u$ into its $\overline{\mathbb Q}$-span;
--   4. $\sum_sc_so_s\mapsto\sum_sc_sM_s\gamma+K_u$ induces a linear isomorphism $W/N\cong\mathbb Q^d/K_u$ intertwining $B_z$ with the operator induced by $M_z$, for every $z\in L_{S_{ret}}$.
--
--   Differences from the source:
--   - generalization: the §4 standing assumption $d\ge1$ → no assumption on $d$; reason: at $d=0$ the statement still holds; dropping a hypothesis only widens the statement
--   - reading: "$K_u$ is $\mathcal K$-invariant" for a rational subspace $K_u$ and $\mathcal K\subseteq GL_d(\overline{\mathbb Q})$ → each $g\in\mathcal K$ maps $K_u$ into the $\overline{\mathbb Q}$-span of $K_u$; reason: the only meaning of the invariance of a rational subspace under $\overline{\mathbb Q}$-points
--   - encoding: the map $\sum_sc_so_s\mapsto\sum_sc_sM_s\gamma+K_u$ induces an isomorphism → an isomorphism $W/N\cong\mathbb Q^d/K_u$ sending the class of each $o_s$ to the class of $M_s\gamma$; reason: a linear map on $W/N$ is determined by its values on the classes of the spanning $o_s$
--   - encoding: $q=\delta(s_0,ue)\in S_{ret}$, stated as part of the setup → a conclusion clause $q\in S_{ret}$; reason: it is a consequence of the construction, not an assumption
--   - encoding: Zariski closure via polynomials in the entries and $\det^{-1}$ → polynomials in the entries, closed sets taken relative to $GL_d(\overline{\mathbb Q})$; reason: multiplying by a power of $\det$, a unit on $GL$, gives the same closed subsets of $GL$
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), Lemma 15, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_CopylessCRA_CCRA
import Definitions.Def_CopylessCRA_IsRep
import Definitions.Def_CopylessCRA_zariskiClosure
import Definitions.Def_CopylessCRA_IsCopylessMap
import Definitions.Def_CopylessCRA_returnWords
open Matrix

namespace CopylessCRA

/-- **Lemma 15 (Local quotients).** Let `u ∈ Σ*`, `q = δ(s0, ue) ∈ S_ret`, and let
`x_u = P_{s0,ue}(x(0))` be the valuation after `ue`. Let `L_{S_ret}` act on `ℚ^r` by `P_z = P_{q,z}`,
and for `s ∈ Σ*` let `o_s = ω_{δ(q,s)} ∘ P_{q,s} ∈ V_r`. Put `W = span{o_s : s ∈ Σ*}`,
`N = {h ∈ W : (B_z h)(x_u) = 0 ∀ z ∈ L_{S_ret}}`,
`K_u = {v ∈ ℚ^d : λ M_{ue} M_z v = 0 ∀ z ∈ L_{S_ret}}`. Then `W` and `N` are invariant under every
`B_z`, `K_u` is `𝒦`-invariant, and `∑_s c_s o_s ↦ ∑_s c_s M_s γ + K_u` induces a linear isomorphism
`W/N ≅ ℚ^d/K_u` intertwining `B_z` with the operator induced by `M_z`, for every `z ∈ L_{S_ret}`.

Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), Lemma 15, p.10 (PDF p.12).

**Formalization Note** The §4 setting: a CCRA `C` computing `f`, a minimal representation
`(λ, M, γ)` of `f` with invertible letter matrices, a word `t` with `|δ(S, t)|` minimal,
`S_ret = δ(S, t)`, `e = t^{|S_ret|!}`. `d ≥ 1` is not assumed (at `d = 0` the statement holds).
`B_z = B_{P_{q,z}}` is the pullback along the composite update. "`K_u` is `𝒦`-invariant" is read
over `ℚ̄`: every `g ∈ 𝒦` maps `K_u` into its `ℚ̄`-span. The isomorphism is given by its values on the
classes of the `o_s`, which determines it. -/
theorem lemma_15 {α : Type*} [Fintype α] (C : CCRA α) [DecidableEq C.S] (f : List α → ℚ)
    (hC : C.Computes f) {d : ℕ} (lam : Fin d → ℚ) (M : α → Matrix (Fin d) (Fin d) ℚ)
    (γ : Fin d → ℚ) (hrep : IsRep f lam M γ) (hmin : IsMinimalRep lam M γ)
    (hM : ∀ a, IsUnit (M a)) (t : List α) (ht : IsMinImageWord C.δ t) (u : List α) :
    deltaWord C.δ C.s0 (u ++ eWord C.δ t) ∈ imageWord C.δ t ∧
    ∃ (hW : ∀ z ∈ returnWords C.δ (imageWord C.δ t), ∀ h ∈ C.localW (deltaWord C.δ C.s0 (u ++ eWord C.δ t)),
        pullback (C.runPoly (deltaWord C.δ C.s0 (u ++ eWord C.δ t)) z) h ∈
          C.localW (deltaWord C.δ C.s0 (u ++ eWord C.δ t)))
      (hN : ∀ z ∈ returnWords C.δ (imageWord C.δ t),
        ∀ h ∈ C.localN (deltaWord C.δ C.s0 (u ++ eWord C.δ t)) (returnWords C.δ (imageWord C.δ t))
          (C.run (u ++ eWord C.δ t)).2,
        pullback (C.runPoly (deltaWord C.δ C.s0 (u ++ eWord C.δ t)) z) h ∈
          C.localN (deltaWord C.δ C.s0 (u ++ eWord C.δ t)) (returnWords C.δ (imageWord C.δ t))
            (C.run (u ++ eWord C.δ t)).2)
      (hK : ∀ z ∈ returnWords C.δ (imageWord C.δ t),
        ∀ v ∈ localK lam M (u ++ eWord C.δ t) (returnWords C.δ (imageWord C.δ t)),
        Matrix.toLin' (wordMat M z) v ∈ localK lam M (u ++ eWord C.δ t) (returnWords C.δ (imageWord C.δ t))),
      (∀ g ∈ returnClosure M (returnWords C.δ (imageWord C.δ t)),
        ∀ v ∈ localK lam M (u ++ eWord C.δ t) (returnWords C.δ (imageWord C.δ t)),
          (g : Matrix (Fin d) (Fin d) Qbar) *ᵥ (fun i => algebraMap ℚ Qbar (v i)) ∈
            Submodule.span Qbar ((fun w : Fin d → ℚ => fun i => algebraMap ℚ Qbar (w i)) ''
              (localK lam M (u ++ eWord C.δ t) (returnWords C.δ (imageWord C.δ t)) :
                Set (Fin d → ℚ)))) ∧
      ∃ φ : (C.localW (deltaWord C.δ C.s0 (u ++ eWord C.δ t)) ⧸
          (C.localN (deltaWord C.δ C.s0 (u ++ eWord C.δ t)) (returnWords C.δ (imageWord C.δ t))
            (C.run (u ++ eWord C.δ t)).2).comap
            (C.localW (deltaWord C.δ C.s0 (u ++ eWord C.δ t))).subtype) ≃ₗ[ℚ]
          ((Fin d → ℚ) ⧸ localK lam M (u ++ eWord C.δ t) (returnWords C.δ (imageWord C.δ t))),
        (∀ s : List α, φ (Submodule.Quotient.mk
            ⟨C.outPoly (deltaWord C.δ C.s0 (u ++ eWord C.δ t)) s, Submodule.subset_span ⟨s, rfl⟩⟩) =
          Submodule.Quotient.mk (wordMat M s *ᵥ γ)) ∧
        ∀ (z : List α) (hz : z ∈ returnWords C.δ (imageWord C.δ t)),
          φ.toLinearMap ∘ₗ quotOp (pullback (C.runPoly (deltaWord C.δ C.s0 (u ++ eWord C.δ t)) z))
              (C.localW (deltaWord C.δ C.s0 (u ++ eWord C.δ t)))
              (C.localN (deltaWord C.δ C.s0 (u ++ eWord C.δ t)) (returnWords C.δ (imageWord C.δ t))
                (C.run (u ++ eWord C.δ t)).2) (hW z hz) (hN z hz) =
            (localK lam M (u ++ eWord C.δ t) (returnWords C.δ (imageWord C.δ t))).mapQ
              (localK lam M (u ++ eWord C.δ t) (returnWords C.δ (imageWord C.δ t)))
              (Matrix.toLin' (wordMat M z)) (fun v hv => hK z hz v hv) ∘ₗ φ.toLinearMap := by sorry

end CopylessCRA
