-- Prove2me | Theorems.Thm_AlonMilman_PropertyT_regularRep_zero_sum_moved
-- name    : AlonMilman.PropertyT.regularRep_zero_sum_moved
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:33:21.1112+00:00
-- url     : https://prove2.me/theorems/9e4bf605-17ee-423f-accf-6fe80cecc29e
-- title:
--   Proof of Lemma 4.8 — the regular representation of a quotient has no fixed zero-sum vector
-- statement:
--   Let $\phi : H \to T$ be a surjective homomorphism from a group $H$ onto a finite group $T$, and let $\pi$ be the left regular representation of $T$ by permutation matrices, $(\pi(t))_{w,u} = 1$ if $w u^{-1} = t$ and $0$ otherwise. Let $W = \{ v \in \mathbb{C}^T : \sum_{t\in T} v_t = 0 \}$. Then every nonzero $v \in W$ is moved by some element of $H$:
--
--   $$v \in W,\ v \ne 0 \;\Longrightarrow\; \exists\, h \in H : \ \pi(\phi(h))\, v \ne v .$$
--
--   In other words the representation $\pi\cdot\phi$ of $H$, restricted to the invariant subspace $W$, is essentially nontrivial (Definition 4.5). This is the claim in the proof of Lemma 4.8 that lets Lemma 4.7 be applied to $W$.
--
--   **Formalization Note** The statement is phrased on the permutation matrices $\pi(\phi(h))$ acting on $\mathbb{C}^T$ rather than on a packaged unitary representation of $H$ in the Hilbert space $W$; the conclusion is exactly the defining condition of essential nontriviality for that representation.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 85, proof of Lemma 4.8

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_regularRep

open Matrix

namespace AlonMilman.PropertyT

/-- Proof of Lemma 4.8 (Alon–Milman 1985, p. 85): for a surjective homomorphism `φ : H →* T`
onto a finite group, the representation `π ∘ φ` (`π` the left regular representation of `T`)
restricted to the zero-sum subspace `W = {v : ∑_t v_t = 0}` is essentially nontrivial: every
nonzero `v ∈ W` is moved by some `π(φ(h))`. -/
theorem regularRep_zero_sum_moved {H T : Type} [Group H] [Group T] [Fintype T] [DecidableEq T]
    (φ : H →* T) (hφ : Function.Surjective φ) (v : T → ℂ) (hv : ∑ t, v t = 0) (hv0 : v ≠ 0) :
    ∃ h : H, regularRep ℂ (φ h) *ᵥ v ≠ v := by sorry

end AlonMilman.PropertyT
