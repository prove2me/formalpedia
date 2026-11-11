-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_proposition_3_1
-- name    : DistributedMWC440.UpperBound.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:26:19.178694+00:00
-- url     : https://prove2.me/theorems/45803890-c236-49e8-b561-0d69828d2a7e
-- title:
--   Proposition 3.1 (Scheduling distributed algorithms) (corrected: polynomially many algorithms)
-- statement:
--   Let a finite collection of independent terminating local protocols run on the same unknown network. Congestion counts, for each undirected edge, how many rounds use that edge across the isolated protocols; dilation is the largest first completion time. The scheduler must reproduce each protocol's local terminal state under a coupling preserving the independent reference tape laws. This is the source scheduling target, rather than a fixed-path timetable statement.
--
--   There is a randomized local scheduler that executes the collection with high probability within
--
--   $$
--   \widetilde O(\operatorname{congestion}(A_1,\ldots,A_r)+\operatorname{dilation}(A_1,\ldots,A_r))
--   $$
--
--   rounds. Every shared-edge transmission is charged, and the output consists of the local terminal states of all isolated algorithms. The number r of algorithms is at most n^a for an arbitrary exponent a fixed before the constants.
--
--   Differences from the source:
--   - encoding: asymptotic O, Omega and high-probability notation → positive constants and a size threshold quantified before the network and varying algorithm parameters; reason: this spells out the uniform asymptotic statement, retaining arbitrary real parameters and fixed polynomial confidence
--   - encoding: concurrent execution of independent algorithms → a local scheduler with a coupling to independent isolated executions, compared at their first global completion times; reason: the coupling preserves both tape marginals and the independent virtual laws; first completion prevents padding the dilation budget
--   - correction: any collection {A_1,…,A_k} → a collection of r ≤ n^a algorithms, for every fixed exponent a (constants may depend on a); reason: with no bound on r the printed statement is false: on a path network, let each of r algorithms make every node send one message on port 0 with probability 1/r in round 0 and halt, so congestion is O(log n) and dilation is 1 w.h.p.; each node's terminal states record which algorithms its neighbour sent in, about log r bits of entropy that must cross the edge, since independent scheduler tapes give the two sides at most log r bits combined; but O(log n)-bit links carry only polylog(n) bits in the allowed time, so for log r ≫ polylog(n) the scheduler fails with constant probability. The source applies it only to Õ(n^{1/k})- and Õ(α^{1+1/k})-size collections, which are polynomial
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, Proposition 3.1, printed p. 14 / PDF p. 16.

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace DistributedMWC440.UpperBound

theorem proposition_3_1 (q b : ℕ) : SchedulingAvailable q b := by sorry

end DistributedMWC440.UpperBound
