-- Prove2me | Theorems.Thm_DecodablePOMDP_lemma_5
-- name    : DecodablePOMDP.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:28:14.015136+00:00
-- url     : https://prove2.me/theorems/b379f721-293f-4dfe-a315-a779ce0209ca
-- title:
--   Lemma 5 — exact belief update on (suffix, weight) pairs
-- statement:
--   Let $\mathcal P$ be a valid POMDP, $\rho\in(0,1]$, $D_h$ decoders with $d_{h,s}\ge\rho$, $L\ge1$, $h\in[1:H-1]$, $u\in\mathcal U_h$ and $w\in\Delta(\mathcal Q)$ supported on $\mathcal A_h(u)$. Let $\beta=\Phi_h(u,w)$, so $\beta(s,q)=w_q\phi^u_{h,q}(s)$. After action $a$ and an alive observation $\tilde z$ with $P(\tilde z\mid\beta,a)>0$ in $\widetilde{\mathcal P}(L)$,
--
--   $$\beta^+=\Phi_{h+1}(u',w'),$$
--
--   where $\beta^+$ is the exact posterior, $u'$ the updated suffix and $w'$ the normalisation (13) of (12). Moreover, $w'$ is supported on $\mathcal A_{h+1}(u')$.
--
--   The representation $(h,u,w)$ is therefore closed under exact filtering.
--
--   Differences from the source:
--   - encoding: "the exact posterior" → the one-step Bayes update of β in P̃(L) (transition T̃_h, then K̃_{h+1}) on (S × Q) ∪ {∂}; reason: this is the posterior of the paper's proof (A.5)
--   - encoding: w supported on A_h(u); a stage h and suffix u (implicit) → w a probability vector, h ∈ [1 : H − 1], u ∈ U_h; reason: the weights the paper updates are probability vectors; actions are taken only at h ≤ H − 1; suffixes have the lengths of Definition 4
--   - generalization: standing assumptions of §3 (ρ ∈ (0, 1], an optimal decoder D_h with (D_h K_h)_{s,s} ≥ ρ, integer L ≥ 1) → any decoder family with d_{h,s} ≥ ρ (`IsRhoDecoderFamily P D ρ`), `0 < ρ ≤ 1`, `1 ≤ L` and `P.IsValid`; reason: the section's standing assumptions (pp.6–8) written as binders; the proofs never use optimality of D_h, so the paper's optimal decoders are a special case
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Lemma 5, p.10 (proof A.5, pp.16–17)

import Mathlib
import Definitions.Def_DecodablePOMDP_Update
import Definitions.Def_DecodablePOMDP_Bayes
import Definitions.Def_DecodablePOMDP_Killed

namespace DecodablePOMDP

open CalibratedCE.Forecast

/-- **Lemma 5 — exact belief update on (suffix, weight) pairs.** Let `P` be a valid POMDP,
`ρ ∈ (0, 1]`, `D_h` decoders with `d_{h,s} ≥ ρ`, `L ≥ 1`, `h ∈ [1 : H−1]`, `u` a suffix of stage
`h`, and `w ∈ Δ(Q)` supported on `A_h(u)`. Let `β = Φ_h(u, w)`. After action `a` and an alive
observation `z̃` with `P(z̃ | β, a) > 0` in `P̃(L)`, the exact posterior is `Φ_{h+1}(u′, w′)`, where
`u′` is the updated suffix and `w′` the normalisation (13) of (12); moreover `w′` is supported on
`A_{h+1}(u′)`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Lemma 5, p.10: "Let β(s, q) = Φh(u, w)(s, q)
= wqϕ^u_{h,q}(s), where w is supported on Ah(u). After taking action a and observing an alive
observation z̃ with positive probability under β, the exact posterior is Φh+1(u′, w′), where u′ is
the updated suffix and w′ is obtained by normalising (12). Moreover, w′ is supported on
Ah+1(u′)."

**Formalization Note.** "The exact posterior" is the one-step Bayes update of `β` in `P̃(L)`
(transition `T̃_h`, then `K̃_{h+1}`), as a vector on `(S × Q) ∪ {∂}`. `h ∈ [1 : H−1]` is the range
where an action is taken; `w` is a probability vector, as are all weights the paper updates. -/
theorem lemma_5 {S A O : Type} [Fintype S] [Fintype A] [Fintype O] [DecidableEq S]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (hP : P.IsValid)
    (hD : IsRhoDecoderFamily P D ρ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 1 ≤ L)
    (h : ℕ) (hh1 : 1 ≤ h) (hhH : h < P.H) (u : Suffix A O S) (hu : IsSuffixAt L h u)
    (w : Option (Fin L) → ℝ) (hw : IsDist w) (hsupp : ∀ q, q ∉ admissibleSet P D ρ L h u → w q = 0)
    (a : A) (z : O × S) (hz : 0 < (killed P D ρ L).obsProb h (Phi P D ρ L h u w) a (some z)) :
    (killed P D ρ L).posterior h (Phi P D ρ L h u w) a (some z) =
        Phi P D ρ L (h + 1) (suffixUpdate L h u a z) (updWeight P D ρ L h u w a z) ∧
    ∀ q, q ∉ admissibleSet P D ρ L (h + 1) (suffixUpdate L h u a z) →
      updWeight P D ρ L h u w a z q = 0 := by sorry

end DecodablePOMDP
