-- Prove2me | Theorems.Thm_DecodablePOMDP_appendix_a10_derandomization
-- name    : DecodablePOMDP.appendix_a10_derandomization
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:01.465306+00:00
-- url     : https://prove2.me/theorems/c43275b0-5bce-4e26-9e6a-099c381f9dbb
-- title:
--   App. A.10, p.20 — derandomisation over decoding tables
-- statement:
--   Let $\mathcal P$ be a valid POMDP, $D_h$ decoders, and $\sigma$ a deterministic policy of the augmented POMDP $\widehat{\mathcal P}$. Running $\sigma$ on $\mathcal P$ while sampling $\widehat X_h\sim D_h(\cdot\mid y_h)$ online is the randomised controller $\Pi$, with value $V^\Pi_{\mathcal P}=V^\sigma_{\widehat{\mathcal P}}$. Then
--
--   1. sampling all decoding-table entries in advance gives the same value:
--   $$V^\Pi_{\mathcal P}=\sum_d\Big(\prod_{h,y}D_h(d_h(y)\mid y)\Big)\,V^{\sigma\circ d}_{\mathcal P};$$
--   2. some table $d$, with every entry in the support of $D_h(\cdot\mid y)$, gives a deterministic policy $\hat\pi=\sigma\circ d$ with $V^{\hat\pi}_{\mathcal P}\ge V^\Pi_{\mathcal P}$.
--
--   This removes the private randomness of the planner without loss of value.
--
--   Differences from the source:
--   - generalization: Π the planner's randomised finite-state controller, with the decoders of §3 → any deterministic policy σ of P̂ and any decoder family; reason: the argument of A.10 uses only that σ is deterministic and that each table entry is used at most once along a trajectory
--   - encoding: V^Π_P (online decoder sampling on P) → V^σ_{P̂}; reason: by the definition of P̂ (p.7), sampling X̂_h ∼ D_h(· | y_h) online and running σ is running σ on P̂
--   - encoding: the resulting controller π̂ → the deterministic history policy σ ∘ d; reason: fixing the table makes the controller deterministic; for a finite-state σ it is the paper's finite-state controller
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), App. A.10, p.20

import Mathlib
import Definitions.Def_DecodablePOMDP_Augmented
import Definitions.Def_DecodablePOMDP_Value
import Definitions.Def_DecodablePOMDP_DecodingTable

namespace DecodablePOMDP

/-- **App. A.10, p.20 — derandomisation over decoding tables.** Let `P` be a valid POMDP and `D_h`
decoders (each `D_h(· | y)` a probability vector). Let `σ` be a deterministic policy of the
augmented POMDP `P̂`; running it on `P` while sampling `X̂_h ∼ D_h(· | y_h)` online is the
randomised controller `Π`, with value `V^Π_P = V^σ_{P̂}`. Then
1. sampling all decoding-table entries `d_h(y) ∼ D_h(· | y)` in advance gives the same value:
   `V^Π_P = Σ_d (Π_{h,y} D_h(d_h(y) | y)) V^{σ∘d}_P`, where `σ∘d` decodes with the table `d`;
2. there is a table `d` with every entry in the support of `D_h(· | y)` whose deterministic policy
   `π̂ = σ∘d` satisfies `V^{π̂}_P ≥ V^Π_P`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.10, p.20: "Finally, independently
sampling all decoding-table entries in advance induces the same trajectory distribution as online
decoder sampling, because each time-indexed entry is used at most once along a trajectory. At each
derandomisation step, the current expected value is a weighted average of the candidate values for
the next entry. Selecting a maximizing candidate therefore cannot decrease the expected value.
After all entries have been fixed, the resulting controller π̂ is deterministic and satisfies
V^π̂_P ≥ V^Π_P."

**Formalization Note.** Stated for every deterministic augmented policy `σ` and every decoder
family (the paper's `σ` is the planner extended to `P̂`, with the decoders of §3). Online decoder
sampling on `P` is, by the definition of `P̂` (p.7), the run of `σ` on `P̂`. -/
theorem appendix_a10_derandomization {S A O : Type} [Fintype S] [Fintype A] [Fintype O]
    [DecidableEq A] [DecidableEq O] [Inhabited S] (P : POMDP S A O) (D : ℕ → O → S → ℝ) (hP : P.IsValid)
    (hD : IsDecoderFamily P D) (σ : DetPolicyFn A (O × S)) :
    value (augmented P D) (toRand σ) =
      ∑ d : Fin (P.H - 1) → O → S,
        tableWeight P.H D d * value P (toRand (decodePolicy P.H d σ)) ∧
    ∃ d : Fin (P.H - 1) → O → S, (∀ i y, 0 < D (i.val + 2) y (d i y)) ∧
      value (augmented P D) (toRand σ) ≤ value P (toRand (decodePolicy P.H d σ)) := by sorry

end DecodablePOMDP
