-- Prove2me | Theorems.Thm_BFAlmostLinear_lemma_4_8
-- name    : BFAlmostLinear.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:19.712967+00:00
-- url     : https://prove2.me/theorems/cfc7a8bf-6be8-4b2a-a5af-dc8043323190
-- title:
--   Lemma 4.8 — weighted $h$-hop searches of total weight $\tilde O(\Lambda hb)$ in $\tilde O(mhb)$ time whp
-- statement:
--   There is a deterministic program and an exponent $a$ with the following properties.
--
--   1. On every weighted graph with frozen flags (auxiliary arcs allowed) satisfying (I1), every hop bound $h$ and every $\lambda\ge0$, the program halts, and when it halts it has output, for every negative vertex $r$, a real $\Delta_r$ and sets $\tilde V^{\mathrm{in}}_r$, $\tilde V^{\mathrm{out}}_r$ such that $\tilde V^{\mathrm{in}}_r$ contains every vertex of every walk of at most $h$ hops (auxiliary arcs allowed) that ends at $r$ and has total weight $<\Delta_r$, and $\tilde V^{\mathrm{out}}_r$ contains every vertex of every walk of at most $h+1$ hops that starts at $r$ and has total weight $<-\Delta_r$.
--   2. For every $d>0$ there is $K$ such that for every such graph on $n$ vertices and $m$ arcs, every $h$, every $\lambda\ge0$ with $\Lambda=\sum_v\lambda(v)$ and every $b\ge1$: if $U$ contains each negative vertex independently with probability $1/b$, then with probability at least $1-n^{-d}$, for every valid potential $\phi$ with
--   $$\tilde d^h_\phi(s,r)+\tilde d^{h+1}_\phi(r,t)\ge0\quad\forall r\in U,\ \forall s,t\in V,$$
--   the program run on $G_\phi$ halts within $K(m+1)(h+1)\,b\,(\log(n+2))^a$ steps and
--   $$\sum_{r\in N}\Big(\sum_{v\in\tilde V^{\mathrm{in}}_r}\lambda(v)+\sum_{v\in\tilde V^{\mathrm{out}}_r}\lambda(v)\Big)\le K\,\Lambda\,(h+1)\,b\,(\log(n+2))^a.$$
--
--   These searches give the sets $V^{\mathrm{in}}_r$, $V^{\mathrm{out}}_r$ of the shortcutting step.
--
--   **Formalization Note** The program does not receive $b$ or $U$. The word bound is $(m+n+h+2)^c$.
--
--   Differences from the source:
--   - reading: "there is an algorithm … runs in $\tilde O(mhb)$ time" → one deterministic program on the mission's machine halting on every input and within $K(m+1)(h+1)b(\log(n+2))^a$ steps on the good event; reason: the paper names no machine; $m+1$, $h+1$ keep $m=0$, $h=0$ non-vacuous.
--   - reading: the printed sum over $V^{\mathrm{in}}_r$, $V^{\mathrm{out}}_r$ → the sum over the computed sets $\tilde V^{\mathrm{in}}_r$, $\tilde V^{\mathrm{out}}_r$; reason: the lemma defines only $\tilde V$, and the proof (p.22) bounds the $\tilde V$ sets, which contain the $V$ sets of §4.3.
--   - encoding: "with high probability", $\Delta_r$ → probability $\ge1-n^{-d}$, finite real $\Delta_r$; reason: footnote 2; an infinite value is replaced by a large finite one.
--   - encoding: frozen flags → hypothesis `Frozen`; reason: §1.1, p.2.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Lemma 4.8, pp.18–19; the bound on Ṽ, p.22

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph_I1
import Definitions.Def_BFAlmostLinear_flagInit

namespace BFAlmostLinear

/-- **Lemma 4.8**, pp.18–19. "Consider a graph G (with auxiliary edges E_fake) that satisfies invariant (I1), with non-negative
weight λ(v) on every vertex v, and a hop bound h. Let Λ = Σ_{v∈V} λ(v) be the total weight. There is an algorithm that, for every
negative vertex r, computes ∆_r with the following sets: • A set Ṽ^in_r that contains all vertices on any h-hop path (which may
use auxiliary edges) that ends at r and whose total weight is less than ∆_r. • A set Ṽ^out_r that contains all vertices on any
(h + 1)-hop path (which may use auxiliary edges) that begins at r and whose total weight is less than −∆_r. Moreover, … Let U ⊆ N
be a random sample where each vertex in N is sampled with probability 1/b. With high probability over the randomness of U, the
following holds. For any valid potential ϕ that satisfies d̃^h_ϕ(s, r) + d̃^{h+1}_ϕ(r, t) ≥ 0, ∀r ∈ U, ∀s, t ∈ V, the algorithm on the
reweighted graph G_ϕ satisfies Σ_{r∈N} (Σ_{v∈V^in_r} λ(v) + Σ_{v∈V^out_r} λ(v)) ≤ Õ(Λhb), and the algorithm runs in Õ(mhb) time."

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Lemma 4.8, pp.18–19.

**Formalization Note.**
* The printed sum has `V`, not `Ṽ`; the proof (p.22) bounds the computed sets, so the bound is on `Ṽ`, which implies the `V` form.
* One deterministic program, with word bound `(m + n + h + 2)^c`. `b` is not an input. The input to the run on `G_ϕ` is `(w_ϕ, flags, λ)`.
* "contains", as printed, so `IsHopSearchOutput` has no upper-set clause beyond the weight bound. `∆_r` is real and may be negative.
* `Õ` is `(log(n + 2))^a`: polylogarithmic in `n` (footnote 1, p.1), with no factor in `h` beyond the printed `h`.
  `h + 1` makes `h = 0` non-vacuous, and `m + 1` makes `m = 0` non-vacuous. -/
theorem lemma_4_8 :
    ∃ (P : Machine.Program) (a : ℕ), Machine.NoCoin P ∧
      (∀ (n m : ℕ) (G : WGraph (Fin n) (Fin m)) (lam : Fin n → ℝ) (h : ℕ),
        G.I1 → G.Frozen → (∀ v, 0 ≤ lam v) →
        let W := Machine.wordBound P (m + n + h + 2)
        let σ₀ := flagInit G 0 h lam
        (∃ T, Machine.HaltsWithin P W Machine.zeroTape σ₀ T) ∧
        ∀ T, Machine.HaltsWithin P W Machine.zeroTape σ₀ T →
          IsHopSearchOutput G h (Machine.run P W Machine.zeroTape σ₀ T)) ∧
      ∀ d : ℝ, 0 < d → ∃ K : ℝ, 0 < K ∧
        ∀ (n m : ℕ) (G : WGraph (Fin n) (Fin m)) (lam : Fin n → ℝ) (h : ℕ) (b : ℝ),
          G.I1 → G.Frozen → (∀ v, 0 ≤ lam v) → 1 ≤ b →
          1 - (n : ℝ) ^ (-d) ≤
            goodMass G.negVertices b fun U =>
              ∀ ϕ : Fin n → ℝ, G.IsValid ϕ →
                (∀ r ∈ U, ∀ s t, 0 ≤ (G.reweight ϕ).dHt h s r + (G.reweight ϕ).dHt (h + 1) r t) →
                let W := Machine.wordBound P (m + n + h + 2)
                let σ₀ := flagInit (G.reweight ϕ) 0 h lam
                let L := Real.log ((n : ℝ) + 2) ^ a
                let T := ⌈K * ((m : ℝ) + 1) * ((h : ℝ) + 1) * b * L⌉₊
                let σ := Machine.run P W Machine.zeroTape σ₀ T
                Machine.HaltsWithin P W Machine.zeroTape σ₀ T ∧
                ∑ r ∈ G.negVertices, (∑ v ∈ listed σ 0 r, lam v + ∑ v ∈ listed σ 1 r, lam v) ≤
                  K * (∑ v, lam v) * ((h : ℝ) + 1) * b * L := by sorry

end BFAlmostLinear
