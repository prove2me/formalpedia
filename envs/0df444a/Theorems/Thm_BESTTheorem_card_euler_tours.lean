-- Prove2me | Theorems.Thm_BESTTheorem_card_euler_tours
-- name    : BESTTheorem.card_euler_tours
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T04:46:38.963943+00:00
-- url     : https://prove2.me/theorems/f6e65855-1e4e-4d9a-927d-53ce8df77e97
-- title:
--   BEST theorem — $\#\text{Euler tours} = N\,\tau_r(G)\prod_v (d^+(v)-1)!$ for balanced multidigraphs
-- statement:
--   **BEST theorem (van Aardenne-Ehrenfest–de Bruijn–Smith–Tutte), labelled-arc counting form, for an arbitrary finite multidigraph.**
--
--   Let $A$ be a finite set of $N \ge 1$ arcs and $V$ a finite set of vertices. Each arc $a$ has a tail $\mathrm{tl}(a)$ and a head $\mathrm{hd}(a)$; loops and parallel arcs are allowed. Write $d^+(v)$ for the number of arcs with tail $v$. Assume the multidigraph is **balanced**: every vertex has as many incoming arcs as outgoing arcs. Fix a root $r$ with at least one out-arc.
--
--   An **Euler tour** is a bijection $\sigma : \{0,\dots,N-1\} \to A$ with $\mathrm{hd}(\sigma(t)) = \mathrm{tl}(\sigma(t+1 \bmod N))$ for every $t$. It is a closed walk using every arc exactly once, recorded together with its starting position, so each cyclic Euler circuit is counted $N$ times.
--
--   Let $S$ be the set of vertices $v \ne r$ with $d^+(v) > 0$. Let $\tau_r$ be the number of **spanning arborescences oriented toward $r$**, counted with arc multiplicities. That is, $\tau_r$ is the sum over parent maps $p : V \to V$ that satisfy
--
--   - $p(v) = v$ for every $v \notin S$, and
--   - every $v \in S$ reaches $r$ by iterating $p$,
--
--   of the product $\prod_{v \in S} \#\{a : \mathrm{tl}(a) = v,\ \mathrm{hd}(a) = p(v)\}$. Then
--   $$\#\{\text{Euler tours}\} \;=\; N \cdot \tau_r \cdot \prod_{v \in V} \bigl(d^+(v) - 1\bigr)!,$$
--   where $(0-1)! = 0! = 1$ for vertices with no arcs.
--
--   Connectivity is not assumed. If the arcs do not form one weakly connected piece, both sides are $0$. As a corollary, $\tau_r$ does not depend on the choice of root $r$.
-- source:
--   R. P. Stanley, Enumerative Combinatorics Vol. 2, Theorem 5.6.2 (BEST theorem); T. van Aardenne-Ehrenfest and N. G. de Bruijn, Circuits and trees in oriented linear graphs, Simon Stevin 28 (1951) 203–217; https://en.wikipedia.org/wiki/BEST_theorem

import Mathlib
open Finset Classical

namespace BESTTheorem

theorem card_euler_tours {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (tl hd : A → V) (hN : 0 < Fintype.card A)
    (hbal : ∀ v, (univ.filter (fun a => hd a = v)).card = (univ.filter (fun a => tl a = v)).card)
    (r : V) (hr : ∃ a, tl a = r) :
    Fintype.card {σ : Fin (Fintype.card A) ≃ A // ∀ t : Fin (Fintype.card A),
        hd (σ t) = tl (σ ⟨(t.val + 1) % Fintype.card A, Nat.mod_lt _ hN⟩)} =
      Fintype.card A *
        (∑ p : V → V,
          if (∀ v, ¬(0 < (univ.filter (fun a => tl a = v)).card ∧ v ≠ r) → p v = v) ∧
              (∀ v, 0 < (univ.filter (fun a => tl a = v)).card → v ≠ r → ∃ k, p^[k] v = r) then
            ∏ v ∈ univ.filter (fun v => 0 < (univ.filter (fun a => tl a = v)).card ∧ v ≠ r),
              (univ.filter (fun a => tl a = v ∧ hd a = p v)).card
          else 0) *
        ∏ v, ((univ.filter (fun a => tl a = v)).card - 1).factorial := by sorry

end BESTTheorem
