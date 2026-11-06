-- Prove2me | Theorems.Thm_DecodablePOMDP_lemma_4
-- name    : DecodablePOMDP.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:27:56.032694+00:00
-- url     : https://prove2.me/theorems/e24dcc10-d0d5-46c7-8375-51688f8e73ed
-- title:
--   Lemma 4 — the conditional state belief depends only on $(h,u_h,q)$
-- statement:
--   Let $\mathcal P$ be a valid POMDP, $\rho\in(0,1]$, $D_h$ decoders with $d_{h,s}\ge\rho$, $L\ge1$, and $\pi$ a randomised policy of $\widetilde{\mathcal P}(L)$. Let $h_h$ be an alive history at a stage $h\le H$ with $\Pr(H_h=h_h)>0$, and $q\in\mathcal Q$ an age with $w_{h,q}(h_h)>0$. Then
--
--   $$\phi_{h,q}(\cdot\,;h_h)=\phi^{u_h}_{h,q},$$
--
--   the suffix calculation of p.10 for the suffix $u_h$ of $h_h$. In particular $\phi_{h,q}$ is determined by $h$, $u_h$ and $q$, and does not depend on the part of the history before $u_h$.
--
--   This is what makes a finite summary of the history sufficient for planning.
--
--   Differences from the source:
--   - generalization: ϕ_{h,q} "is determined by the time h, the recent suffix u_h, and q" → ϕ_{h,q}(·; h_h) equals the explicit function ϕ^{u_h}_{h,q} of p.10; reason: naming the function of (h, u_h, q) implies that ϕ_{h,q} is determined by them; it is the function the paper's proof computes (A.4)
--   - encoding: "every alive history h_h" (latest observation not †) and ϕ_{h,q} defined by (5) → histories with every observation in O × S, Pr(H_h = h_h) > 0, w_{h,q} > 0, stage h ≤ H; reason: † is absorbing, so a positive-probability history whose latest observation is alive has none; (5) defines ϕ_{h,q} only when w_{h,q} > 0 and Pr(H_h = h_h) > 0 (p.9)
--   - encoding: probabilities in P̃(L) (policy implicit) → probabilities under an arbitrary randomised policy π of P̃(L); reason: the statement holds for every policy; the paper leaves the policy implicit
--   - generalization: standing assumptions of §3 (ρ ∈ (0, 1], an optimal decoder D_h with (D_h K_h)_{s,s} ≥ ρ, integer L ≥ 1) → any decoder family with d_{h,s} ≥ ρ (`IsRhoDecoderFamily P D ρ`), `0 < ρ ≤ 1`, `1 ≤ L` and `P.IsValid`; reason: the section's standing assumptions (pp.6–8) written as binders; the proofs never use optimality of D_h, so the paper's optimal decoders are a special case
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Lemma 4, p.10 (proof A.4, p.16)

import Mathlib
import Definitions.Def_DecodablePOMDP_Posterior
import Definitions.Def_DecodablePOMDP_Admissible

namespace DecodablePOMDP

/-- **Lemma 4 — the conditional state belief depends only on `(h, u_h, q)`.** Let `P` be a valid
POMDP, `ρ ∈ (0, 1]`, `D_h` decoders with `d_{h,s} ≥ ρ`, `L ≥ 1`, and `π` any randomised policy of
`P̃(L)`. For every alive history `h_h` of `P̃(L)` at stage `h = t + 1 ≤ H` with
`Pr(H_h = h_h) > 0` and every age `q ∈ Q` with `w_{h,q}(h_h) > 0`, the conditional state belief
`ϕ_{h,q}(·; h_h)` equals the suffix calculation `ϕ^{u_h}_{h,q}` of p.10, which depends only on
`h`, the suffix `u_h` of `h_h` and `q`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Lemma 4, p.10: "For every alive history hh
and every q ∈ Q, the conditional state belief ϕh,q is determined by the time h, the recent suffix
uh, and the time since last reveal q. Notably, it is independent of the part of the history before
uh."

**Formalization Note.** `ϕ_{h,q}` is defined by (5) only when `w_{h,q} > 0` and
`Pr(H_h = h_h) > 0` (p.9), which are the hypotheses. An alive history has every observation in
`O × S` (`†` is absorbing, so a positive-probability history whose latest observation is alive has
no `†`). The conclusion names the function of `(h, u_h, q)`: the suffix calculation of p.10. -/
theorem lemma_4 {S A O : Type} [Fintype S] [Fintype A] [Fintype O] [DecidableEq S]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (hP : P.IsValid)
    (hD : IsRhoDecoderFamily P D ρ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 1 ≤ L)
    (π : PolicyFn A (Option (O × S))) (hπ : IsRandPolicy π) (t : ℕ) (ht : t + 1 ≤ P.H)
    (hist : Hist A (O × S) t) (q : Option (Fin L))
    (hpos : 0 < histProb P D ρ L π t hist) (hw : 0 < posteriorWeight P D ρ L π t hist q) :
    posteriorState P D ρ L π t hist q = phiU P D ρ L (t + 1) (suffixOf L t hist) q := by sorry

end DecodablePOMDP
