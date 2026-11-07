-- Prove2me | Theorems.Thm_EulerianLE_lemma_32
-- name    : EulerianLE.lemma_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:58:53.792586+00:00
-- url     : https://prove2.me/theorems/5856e519-936f-4ceb-924d-08b6e5d7b941
-- title:
--   Lemma 32 — the OR protocol on an oriented circuit
-- statement:
--   Consider an execution of an arbitrary algorithm, written in the language `Code`, in which OR instances $x_0,x_1,\dots,x_k$ run on an oriented circuit $C$: $x_0$ is the OR initiator (Program 7), $x_1,\dots,x_k$ are participants (Program 8) in CW order, the edge at the outgoing CW port of $x_h$ leads to the incoming CW port of $x_{h+1}$ (indices modulo $k+1$), and $b_h$ is the input of $x_h$. Suppose that $x_0$ starts at time $t_0$ and that
--
--   1. (i) at $t_0$ no pulse is queued at a port on $C$ or in transit to one;
--   2. (ii) until $x_0$ returns, only the instances send through or consume at ports on $C$, and no node completes before all its instances on $C$ have returned;
--   3. (iii) at $t_0$ each $x_h$, $h\ge1$, is at its initial wait (Line 3 of Program 8) or has not started; in the latter case it starts, with input $b_h$, once its node is awake and a pulse is waiting at one of its ports, with no further wake-up or delivery.
--
--   Then every instance returns, having consumed every pulse that the instances send to its ports, and $x_0$ returns last. Every instance returns
--   $$b_1\vee\cdots\vee b_k\qquad(\text{so }0\text{ if }k=0)$$
--   as its output bit; if this bit is $1$, exactly one instance returns $(1,\text{witness})$, namely $x_m$ for the least $m$ with $b_m=1$.
--
--   The lemma is the black box through which the Check node decides whether some other circuit still contains a Counting node.
--
--   Differences from the source:
--   - generalization: the paper's network: a finite connected undirected Eulerian graph → any port-numbered multigraph (`Network`), with no Eulerian or connectivity hypothesis; reason: the statement concerns arbitrary algorithms and does not use the Eulerian property; Eulerian networks are a special case
--   - encoding: a scheduler generating WakeUp and PulseDeliver events, each after finitely many others; local computation takes no time → a fair run (`Run`, `IsFair`) in which wake-ups and deliveries occur only when no node can execute an instruction; reason: "Local computation takes no time" and "No delivery occurs between operations that a node performs at the same time" (pp.8, 10); the executions are the same
--   - reading: "an execution in which the OR protocol runs on an oriented circuit C" in an arbitrary surrounding algorithm → any program texts in the language `Code` (with Programs 7 and 8 built in), any variables, outputs and phase labels, in a fair run; an instance is a thread at an OR program point on its port pair; reason: Programs 1–8 are written in this language; the hypotheses (i)–(iii) are stated on the run, as in the source
--   - reading: (ii) "until x0 returns, … and no node completes … before all its instances on C have returned" → both clauses of (ii) are required only until x0 returns; reason: the scope of "until x0 returns" is ambiguous; this reading is the weaker hypothesis, so the statement is the stronger one
--   - encoding: "returns", "after consuming every pulse that the instances send to its ports", "x0 returns last" → the first time τ_h ≥ t₀ at which x_h is at the program point `ret`; at τ_h each port p of x_h has consumed since t₀ as many pulses as were sent through link p between t₀ and τ_0; τ_h < τ_0 for h ≠ 0; reason: τ_0 is the return of x0, after which no instance sends
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), App. C.5, p.43 (PDF p.45), Lemma 32

import Mathlib
import Definitions.Def_EulerianLE_VNode

namespace EulerianLE

/-- **Lemma 32** (OR on a circuit; Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), App. C.5, p.43, PDF p.45). Consider
an execution in which the OR protocol runs on an oriented circuit `C`. Let `x₀` be the OR initiator,
`x₁, …, x_k` the other participants in CW order, and `b_h` the input of `x_h`. Suppose that `x₀` starts and
that
(i) when `x₀` starts, no pulse is queued at a port on `C` or in transit to one;
(ii) until `x₀` returns, only the instances send pulses through ports on `C` or consume pulses at them,
and no node completes the algorithm in which these instances run before all its instances on `C` have
returned;
(iii) when `x₀` starts, each `x_h` with `h ≥ 1` is at its initial wait (Line 3 of Program 8) or has not
started; in the latter case, it starts once its node is awake and a pulse is waiting at one of its
ports, and needs no further wake-up or delivery to do so.
Then every instance returns, after consuming every pulse that the instances send to its ports, and `x₀`
returns last. The output bit of every instance is `b₁ ∨ ⋯ ∨ b_k` (so `0` if `k = 0`); if it is `1`, exactly
one instance returns `(1, witness)`, namely `x_m` for the least `m` with `b_m = 1`.

**Formalization Note.** The surrounding algorithm is arbitrary: any program texts `code v` (with any
variables, initial values and outputs), interpreted by `Code.prog`, run under any phase labels `tag`, in
a fair run `ρ`. An OR instance is a thread of a node running the built-in Programs 7/8 (`ORLine`) on a
port pair; `x h` gives its node, thread, incoming CW port and outgoing CW port. The circuit `C` is
oriented by "the edge at the outgoing CW port of `x_h` leads to the incoming CW port of `x_{h+1}`"
(indices mod `k + 1`), and uses each port once; distinct instances use distinct threads. `x₀` starts at
time `t₀` (it is at Line 3 of Program 7). `b h` is the input with which `x_h` is, or will be, called;
`b 0` is not used. "Returns `o`" is: the instance's program point is `ret o`; `τ h` is the first such time
from `t₀` on. "After consuming every pulse that the instances send to its ports": at `τ h`, each port `p` of
`x_h` has consumed, since `t₀`, as many pulses as were sent through `link p` between `t₀` and `τ 0`, the return
of `x₀`, after which by the conclusion no instance sends. In (ii), the operation that changes the
counters of a port of `x_h` is performed by `x_h`'s thread (whose stack changes in that step). -/
theorem lemma_32 {G : Network} {S Out : G.V → Type} (code : ∀ v, Code (G.deg v) (S v))
    (s₀ : ∀ v, S v) (fin : ∀ v, Ctx (G.deg v) (S v) → Out v) (tag : Tag (codeProgs code s₀ fin))
    (ρ : Run (codeProgs code s₀ fin) tag) (hρ : IsFair ρ)
    (k : ℕ) (x : Fin (k + 1) → VNode G) (b : Fin (k + 1) → Bool)
    (hcirc : ∀ h, G.link (x h).outPort = (x (h + 1)).inPort)
    (hports : Function.Injective fun hb : Fin (k + 1) × Bool =>
      if hb.2 then (x hb.1).inPort else (x hb.1).outPort)
    (hloc : ∀ h h', (x h).v = (x h').v → (x h).loc = (x h').loc → h = h')
    (t₀ : ℕ) (hstart : ρ.orLineAt (x 0) t₀ = some .i3)
    (h_i : ∀ h, ∀ p ∈ [(x h).inPort, (x h).outPort],
      (ρ.cfg t₀).queue p = [] ∧ (ρ.cfg t₀).transit p = [])
    (h_ii : ∀ t, t₀ ≤ t →
      (∀ t', t₀ ≤ t' → t' ≤ t → ∀ o, ρ.orLineAt (x 0) t' ≠ some (.ret o)) →
      (∀ h, ∀ p ∈ [(x h).inPort, (x h).outPort],
          ((ρ.cfg (t + 1)).sent p ≠ (ρ.cfg t).sent p ∨
            (ρ.cfg (t + 1)).consumed p ≠ (ρ.cfg t).consumed p) →
          (ρ.orLineAt (x h) t).isSome ∧ ρ.threadAt (x h) (t + 1) ≠ ρ.threadAt (x h) t) ∧
      (∀ h, ρ.CompletesAt (x h).v t →
          ∃ t', t₀ ≤ t' ∧ t' ≤ t ∧ ∃ o, ρ.orLineAt (x h) t' = some (.ret o)))
    (h_iii : ∀ h, h ≠ 0 →
      ρ.orLineAt (x h) t₀ = some (.p3 (b h)) ∨
      ((∀ t', t' ≤ t₀ → ρ.orLineAt (x h) t' = none) ∧
        ∀ t, t₀ ≤ t → (∀ t', t' ≤ t → ρ.orLineAt (x h) t' = none) →
          (∃ s, (ρ.cfg t).status (x h).v = .running s) →
          ((ρ.cfg t).queue (x h).inPort ≠ [] ∨ (ρ.cfg t).queue (x h).outPort ≠ []) →
          ∃ t₁, t ≤ t₁ ∧ (∀ t', t ≤ t' → t' < t₁ → ∃ w, ρ.ev t' = some (.op w)) ∧
            ρ.orLineAt (x h) t₁ = some (.p3 (b h)))) :
    ∃ τ : Fin (k + 1) → ℕ,
      (∀ h, t₀ ≤ τ h ∧ ρ.orLineAt (x h) (τ h) = some (.ret (orExpected b h)) ∧
        (∀ t o, t₀ ≤ t → t < τ h → ρ.orLineAt (x h) t ≠ some (.ret o)) ∧
        ∀ p ∈ [(x h).inPort, (x h).outPort],
          (ρ.cfg (τ h)).consumed p + (ρ.cfg t₀).sent (G.link p) =
            (ρ.cfg t₀).consumed p + (ρ.cfg (τ 0)).sent (G.link p)) ∧
      ∀ h, h ≠ 0 → τ h < τ 0 := by sorry

end EulerianLE
